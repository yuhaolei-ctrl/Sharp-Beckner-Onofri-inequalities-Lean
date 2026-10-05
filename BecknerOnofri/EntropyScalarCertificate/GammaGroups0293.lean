module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0366
public import BecknerOnofri.EntropyScalarCertificate.Bessel0367
public import BecknerOnofri.EntropyScalarCertificate.Bessel0672
public import BecknerOnofri.EntropyScalarCertificate.Brackets0146
public import BecknerOnofri.EntropyScalarCertificate.Brackets0147
public import BecknerOnofri.EntropyScalarCertificate.Logs0293
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2344
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (187843175605594284831314670079532591577317/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (187843175605594284831314670079532591577317/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (18924573520477343695168804309548555999607/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18924573520477343695168804309548555999607/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (377088910810367721783002713175018151573387/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (377088910810367721783002713175018151573387/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2344 BracketBatch0146.bracket2345 (377088910810367721783002713175018151573387/20000000000000000000000000000000000000000) (3606210959940183270551568764040219838243/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2344 BracketBatch0146.bracket2345
  (377088910810367721783002713175018151573387/20000000000000000000000000000000000000000) (3606210959940183270551568764040219838243/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2344
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2345
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (189245735204773436951688043095485559996067/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (189245735204773436951688043095485559996067/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (190669548862629808920084905498720965617603/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (190669548862629808920084905498720965617603/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (37991528406740324587177294859420652561367/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37991528406740324587177294859420652561367/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2345 BracketBatch0146.bracket2346 (37991528406740324587177294859420652561367/2000000000000000000000000000000000000000) (3616096534832788656448838979064106966193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2345 BracketBatch0146.bracket2346
  (37991528406740324587177294859420652561367/2000000000000000000000000000000000000000) (3616096534832788656448838979064106966193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2345
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2346
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (119168468039143630575053065936700603511/6250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (119168468039143630575053065936700603511/6250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (19211510331068145512906260055815951628759/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19211510331068145512906260055815951628759/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (38278465217331126404914750605688048190519/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38278465217331126404914750605688048190519/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2346 BracketBatch0146.bracket2347 (38278465217331126404914750605688048190519/2000000000000000000000000000000000000000) (362605009273946116901229128682763444419/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2346 BracketBatch0146.bracket2347
  (38278465217331126404914750605688048190519/2000000000000000000000000000000000000000) (362605009273946116901229128682763444419/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2346
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2347
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (192115103310681455129062600558159516287587/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (192115103310681455129062600558159516287587/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (193582900256805399123479146605876928639391/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (193582900256805399123479146605876928639391/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (192849001783743427126270873582018222463489/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (192849001783743427126270873582018222463489/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2347 BracketBatch0146.bracket2348 (192849001783743427126270873582018222463489/10000000000000000000000000000000000000000) (90901807092648561516201035177145820707/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2347 BracketBatch0146.bracket2348
  (192849001783743427126270873582018222463489/10000000000000000000000000000000000000000) (90901807092648561516201035177145820707/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2347
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2348
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (48395725064201349780869786651469232159847/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (48395725064201349780869786651469232159847/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (195073456965716649852205645276120244656753/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (195073456965716649852205645276120244656753/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (388656357222522048975684791881997173296141/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (388656357222522048975684791881997173296141/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2348 BracketBatch0146.bracket2349 (388656357222522048975684791881997173296141/20000000000000000000000000000000000000000) (1823081878086134504806191446783102579729/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2348 BracketBatch0146.bracket2349
  (388656357222522048975684791881997173296141/20000000000000000000000000000000000000000) (1823081878086134504806191446783102579729/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2348
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2349
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (780293827862866599408822581104480978627/40000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (780293827862866599408822581104480978627/40000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (39317461373331434373653973075603350034261/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (39317461373331434373653973075603350034261/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (78332152766474764344095102130827398965611/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (78332152766474764344095102130827398965611/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2349 BracketBatch0146.bracket2350 (78332152766474764344095102130827398965611/4000000000000000000000000000000000000000) (3656325156106224810198205339525651049809/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2349 BracketBatch0146.bracket2350
  (78332152766474764344095102130827398965611/4000000000000000000000000000000000000000) (3656325156106224810198205339525651049809/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2349
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2350
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (98293653433328585934134932689008375085651/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98293653433328585934134932689008375085651/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (99062500094897285359142548061122365333569/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (99062500094897285359142548061122365333569/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (9867807676411293564663874037506537020961/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9867807676411293564663874037506537020961/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2350 BracketBatch0146.bracket2351 (9867807676411293564663874037506537020961/500000000000000000000000000000000000000) (3666557126056168161990532192115735697233/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2350 BracketBatch0146.bracket2351
  (9867807676411293564663874037506537020961/500000000000000000000000000000000000000) (3666557126056168161990532192115735697233/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2350
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2351
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (39625000037958914143657019224448946133427/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39625000037958914143657019224448946133427/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0367.rows BesselBatch0367.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (4992177615823136942448727203429401874679/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4992177615823136942448727203429401874679/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (79562420964544009683246836851884161130859/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (79562420964544009683246836851884161130859/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0293.rows ScalarLogs0293.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2351 BracketBatch0147.bracket2352 (79562420964544009683246836851884161130859/4000000000000000000000000000000000000000) (735372060823268552495778767985445086429/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2351 BracketBatch0147.bracket2352
  (79562420964544009683246836851884161130859/4000000000000000000000000000000000000000) (735372060823268552495778767985445086429/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2351
