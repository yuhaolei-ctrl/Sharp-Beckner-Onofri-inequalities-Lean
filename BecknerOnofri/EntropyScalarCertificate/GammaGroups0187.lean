import BecknerOnofri.EntropyScalarCertificate.Bessel0233
import BecknerOnofri.EntropyScalarCertificate.Bessel0234
import BecknerOnofri.EntropyScalarCertificate.Bessel0235
import BecknerOnofri.EntropyScalarCertificate.Bessel0605
import BecknerOnofri.EntropyScalarCertificate.Bessel0606
import BecknerOnofri.EntropyScalarCertificate.Brackets0093
import BecknerOnofri.EntropyScalarCertificate.Brackets0094
import BecknerOnofri.EntropyScalarCertificate.Logs0187
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1496
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (702677624066000345508954104514111335103/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (702677624066000345508954104514111335103/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (17576603852202027918792293285731071339763/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17576603852202027918792293285731071339763/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (17571772226926018278258072949291927358669/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17571772226926018278258072949291927358669/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1496 BracketBatch0093.bracket1497 (17571772226926018278258072949291927358669/10000000000000000000000000000000000000000) (673038731781387492150582721762398411043/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1496 BracketBatch0093.bracket1497
  (17571772226926018278258072949291927358669/10000000000000000000000000000000000000000) (673038731781387492150582721762398411043/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1496
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1497
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (219707548152525348984903666071638391747/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (219707548152525348984903666071638391747/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (17586279271252873269397594815190882389853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17586279271252873269397594815190882389853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (35162883123454901188189888100921953729613/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35162883123454901188189888100921953729613/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1497 BracketBatch0093.bracket1498 (35162883123454901188189888100921953729613/20000000000000000000000000000000000000000) (134712814460760349697768264018484441477/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1497 BracketBatch0093.bracket1498
  (35162883123454901188189888100921953729613/20000000000000000000000000000000000000000) (134712814460760349697768264018484441477/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1497
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1498
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (351725585425057465387951896303817647797/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (351725585425057465387951896303817647797/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (3519193376690214876478129694461183822609/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3519193376690214876478129694461183822609/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (7036449230940789530357648657499360300579/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7036449230940789530357648657499360300579/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1498 BracketBatch0093.bracket1499 (7036449230940789530357648657499360300579/4000000000000000000000000000000000000000) (84261244515135171199692265761333571181/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1498 BracketBatch0093.bracket1499
  (7036449230940789530357648657499360300579/4000000000000000000000000000000000000000) (84261244515135171199692265761333571181/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1498
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1499
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (8797983441725537191195324236152959556521/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8797983441725537191195324236152959556521/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (17605666713509094965266084570157359737191/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17605666713509094965266084570157359737191/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (35201633596960169347656733042463278850233/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35201633596960169347656733042463278850233/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1499 BracketBatch0093.bracket1500 (35201633596960169347656733042463278850233/20000000000000000000000000000000000000000) (337308192027284344100505783545317331797/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1499 BracketBatch0093.bracket1500
  (35201633596960169347656733042463278850233/20000000000000000000000000000000000000000) (337308192027284344100505783545317331797/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1499
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1500
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (4401416678377273741316521142539339934297/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4401416678377273741316521142539339934297/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (8807689393101765360661968428155759950811/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8807689393101765360661968428155759950811/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (3522104549971262568659002142646887963881/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3522104549971262568659002142646887963881/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1500 BracketBatch0093.bracket1501 (3522104549971262568659002142646887963881/2000000000000000000000000000000000000000) (675143356927146529037924315090316552571/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1500 BracketBatch0093.bracket1501
  (3522104549971262568659002142646887963881/2000000000000000000000000000000000000000) (675143356927146529037924315090316552571/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1500
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1501
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (17615378786203530721323936856311519901619/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17615378786203530721323936856311519901619/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (17625103126375308046457523012232628973579/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17625103126375308046457523012232628973579/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (17620240956289419383890729934272074437599/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17620240956289419383890729934272074437599/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1501 BracketBatch0093.bracket1502 (17620240956289419383890729934272074437599/10000000000000000000000000000000000000000) (675670875563241248874649503961339732627/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1501 BracketBatch0093.bracket1502
  (17620240956289419383890729934272074437599/10000000000000000000000000000000000000000) (675670875563241248874649503961339732627/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1501
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1502
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2203137890796913505807190376529078621697/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2203137890796913505807190376529078621697/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (8817419879464941722305729177183530601767/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8817419879464941722305729177183530601767/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (3525994288530519149106898136659969017711/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3525994288530519149106898136659969017711/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1502 BracketBatch0093.bracket1503 (3525994288530519149106898136659969017711/2000000000000000000000000000000000000000) (338099470394412891357835558813110757569/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1502 BracketBatch0093.bracket1503
  (3525994288530519149106898136659969017711/2000000000000000000000000000000000000000) (338099470394412891357835558813110757569/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1502
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1503
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0234.rows BesselBatch0234.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (17634839758929883444611458354367061203531/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17634839758929883444611458354367061203531/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0235.rows BesselBatch0235.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (17644588708837443664969225604708420581013/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17644588708837443664969225604708420581013/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0606.rows BesselBatch0606.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1102482139617728972174396373721108805767/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1102482139617728972174396373721108805767/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0187.rows ScalarLogs0187.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1503 BracketBatch0094.bracket1504 (1102482139617728972174396373721108805767/625000000000000000000000000000000000000) (338363776715711348115457904455501762429/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1503 BracketBatch0094.bracket1504
  (1102482139617728972174396373721108805767/625000000000000000000000000000000000000) (338363776715711348115457904455501762429/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1503
