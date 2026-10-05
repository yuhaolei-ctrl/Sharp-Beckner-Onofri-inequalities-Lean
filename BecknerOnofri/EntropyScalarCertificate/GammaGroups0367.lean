import BecknerOnofri.EntropyScalarCertificate.Bessel0458
import BecknerOnofri.EntropyScalarCertificate.Bessel0459
import BecknerOnofri.EntropyScalarCertificate.Bessel0460
import BecknerOnofri.EntropyScalarCertificate.Bessel0718
import BecknerOnofri.EntropyScalarCertificate.Brackets0183
import BecknerOnofri.EntropyScalarCertificate.Brackets0184
import BecknerOnofri.EntropyScalarCertificate.Logs0367
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2936
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1276763897221000845213839014580092741340377/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1276763897221000845213839014580092741340377/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1280026062188224523482769690588645669725587/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1280026062188224523482769690588645669725587/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (639197489852306342174152176292184602766491/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (639197489852306342174152176292184602766491/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2936 BracketBatch0183.bracket2937 (639197489852306342174152176292184602766491/5000000000000000000000000000000000000000) (6489695114303224262387361883761077785369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2936 BracketBatch0183.bracket2937
  (639197489852306342174152176292184602766491/5000000000000000000000000000000000000000) (6489695114303224262387361883761077785369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2936
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2937
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (80001628886764032717673105661790354357849/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (80001628886764032717673105661790354357849/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (80206559765959649086794866250710945800901/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (80206559765959649086794866250710945800901/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (128166550922178945443574377530001040127/1000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (128166550922178945443574377530001040127/1000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2937 BracketBatch0183.bracket2938 (128166550922178945443574377530001040127/1000000000000000000000000000000000000) (1623405300575491337421454991399456629827/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2937 BracketBatch0183.bracket2938
  (128166550922178945443574377530001040127/1000000000000000000000000000000000000) (1623405300575491337421454991399456629827/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2937
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2938
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1283304956255354385388717860011375132814413/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1283304956255354385388717860011375132814413/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (643300354219291609561690500071726911501889/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (643300354219291609561690500071726911501889/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (2569905664693937604512098860154828955818191/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2569905664693937604512098860154828955818191/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2938 BracketBatch0183.bracket2939 (2569905664693937604512098860154828955818191/20000000000000000000000000000000000000000) (3248778591591667990470679982627194749359/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2938 BracketBatch0183.bracket2939
  (2569905664693937604512098860154828955818191/20000000000000000000000000000000000000000) (3248778591591667990470679982627194749359/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2938
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2939
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (51464028337543328764935240005738152920151/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (51464028337543328764935240005738152920151/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1289913449084167656196478751830067418392341/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1289913449084167656196478751830067418392341/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (644128539380687718829964937993380310349029/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (644128539380687718829964937993380310349029/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2939 BracketBatch0183.bracket2940 (644128539380687718829964937993380310349029/5000000000000000000000000000000000000000) (203171971981852297409901695345709565791/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2939 BracketBatch0183.bracket2940
  (644128539380687718829964937993380310349029/5000000000000000000000000000000000000000) (203171971981852297409901695345709565791/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2939
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2940
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (644956724542083828098239375915033709196169/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (644956724542083828098239375915033709196169/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (646621654942806229408552446874024154688117/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (646621654942806229408552446874024154688117/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (645789189742445028753395911394528931942143/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (645789189742445028753395911394528931942143/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2940 BracketBatch0183.bracket2941 (645789189742445028753395911394528931942143/5000000000000000000000000000000000000000) (6505459009784250046124973483740604284877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2940 BracketBatch0183.bracket2941
  (645789189742445028753395911394528931942143/5000000000000000000000000000000000000000) (6505459009784250046124973483740604284877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2940
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2941
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1293243309885612458817104893748048309376231/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1293243309885612458817104893748048309376231/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1296590423901121920550437122756531757540149/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1296590423901121920550437122756531757540149/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (129491686689336718968377100825229003345819/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (129491686689336718968377100825229003345819/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2941 BracketBatch0183.bracket2942 (129491686689336718968377100825229003345819/1000000000000000000000000000000000000000) (1301884989871506534815292193577256011103/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2941 BracketBatch0183.bracket2942
  (129491686689336718968377100825229003345819/1000000000000000000000000000000000000000) (1301884989871506534815292193577256011103/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2941
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2942
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (648295211950560960275218561378265878770073/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (648295211950560960275218561378265878770073/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1299954925571323236854811145880650878258637/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1299954925571323236854811145880650878258637/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (2596545349472445157405248268637182635798783/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2596545349472445157405248268637182635798783/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2942 BracketBatch0183.bracket2943 (2596545349472445157405248268637182635798783/20000000000000000000000000000000000000000) (6513400969525457606050615691202278367543/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2942 BracketBatch0183.bracket2943
  (2596545349472445157405248268637182635798783/20000000000000000000000000000000000000000) (6513400969525457606050615691202278367543/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2942
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2943
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0459.rows BesselBatch0459.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (649977462785661618427405572940325439129317/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (649977462785661618427405572940325439129317/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0460.rows BesselBatch0460.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (651668475368633401641718279179102072901319/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (651668475368633401641718279179102072901319/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (325411484538573755017280963029856878007659/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (325411484538573755017280963029856878007659/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0367.rows ScalarLogs0367.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2943 BracketBatch0184.bracket2944 (325411484538573755017280963029856878007659/2500000000000000000000000000000000000000) (6517387117983717913210911663642295597891/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2943 BracketBatch0184.bracket2944
  (325411484538573755017280963029856878007659/2500000000000000000000000000000000000000) (6517387117983717913210911663642295597891/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2943
