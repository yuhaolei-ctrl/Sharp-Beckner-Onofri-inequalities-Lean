module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0187
public import BecknerOnofri.EntropyScalarCertificate.Bessel0188
public import BecknerOnofri.EntropyScalarCertificate.Bessel0582
public import BecknerOnofri.EntropyScalarCertificate.Bessel0583
public import BecknerOnofri.EntropyScalarCertificate.Brackets0075
public import BecknerOnofri.EntropyScalarCertificate.Logs0150
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1200
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (4768982513776989819729230010084337284509/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4768982513776989819729230010084337284509/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (9566222988720820374047739425849445709697/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9566222988720820374047739425849445709697/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (3820837603254960002701239889203624055743/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3820837603254960002701239889203624055743/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1200 BracketBatch0075.bracket1201 (3820837603254960002701239889203624055743/4000000000000000000000000000000000000000) (216533655755701824278815112609247334957/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1200 BracketBatch0075.bracket1201
  (3820837603254960002701239889203624055743/4000000000000000000000000000000000000000) (216533655755701824278815112609247334957/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1200
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1201
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (4783111494360410187023869712924722854847/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4783111494360410187023869712924722854847/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (9594614398759109021693968480180012266059/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9594614398759109021693968480180012266059/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (19160837387479929395741707906029457975753/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19160837387479929395741707906029457975753/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1201 BracketBatch0075.bracket1202 (19160837387479929395741707906029457975753/20000000000000000000000000000000000000000) (43608251989122762212348869311751973081/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1201 BracketBatch0075.bracket1202
  (19160837387479929395741707906029457975753/20000000000000000000000000000000000000000) (43608251989122762212348869311751973081/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1201
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1202
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1199326799844888627711746060022501533257/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1199326799844888627711746060022501533257/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (120289256916046913672724766925685970761/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (120289256916046913672724766925685970761/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (2402219369005357764438993729279361240867/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2402219369005357764438993729279361240867/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1202 BracketBatch0075.bracket1203 (2402219369005357764438993729279361240867/2500000000000000000000000000000000000000) (219558610048476426899375830079807686181/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1202 BracketBatch0075.bracket1203
  (2402219369005357764438993729279361240867/2500000000000000000000000000000000000000) (219558610048476426899375830079807686181/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1202
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1203
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0187.rows BesselBatch0187.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (9623140553283753093817981354054877660877/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9623140553283753093817981354054877660877/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (482590138263958710110272990804002059707/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (482590138263958710110272990804002059707/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (19274943318562927296023441170134918855017/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19274943318562927296023441170134918855017/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1203 BracketBatch0075.bracket1204 (19274943318562927296023441170134918855017/20000000000000000000000000000000000000000) (1768686224998201514472378384999466959/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1203 BracketBatch0075.bracket1204
  (19274943318562927296023441170134918855017/20000000000000000000000000000000000000000) (1768686224998201514472378384999466959/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1203
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1204
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (9651802765279174202205459816080041194137/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9651802765279174202205459816080041194137/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (9680602365395621345262622508185664615377/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9680602365395621345262622508185664615377/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0582.rows BesselBatch0582.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (9666202565337397773734041162132852904757/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9666202565337397773734041162132852904757/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1204 BracketBatch0075.bracket1205 (9666202565337397773734041162132852904757/10000000000000000000000000000000000000000) (222622837022955831051110592077702121663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1204 BracketBatch0075.bracket1205
  (9666202565337397773734041162132852904757/10000000000000000000000000000000000000000) (222622837022955831051110592077702121663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1204
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1205
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (4840301182697810672631311254092832307687/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4840301182697810672631311254092832307687/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (121369258778144321445776598902553044503/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (121369258778144321445776598902553044503/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (9695071533823583530462375210194954087807/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9695071533823583530462375210194954087807/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1205 BracketBatch0075.bracket1206 (9695071533823583530462375210194954087807/10000000000000000000000000000000000000000) (224169846105123702369739154547708847423/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1205 BracketBatch0075.bracket1206
  (9695071533823583530462375210194954087807/10000000000000000000000000000000000000000) (224169846105123702369739154547708847423/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1205
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1206
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (9709540702251545715662127912204243560237/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9709540702251545715662127912204243560237/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (9738619142742180472810139105999454301487/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9738619142742180472810139105999454301487/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (4862039961248431547118066754550924465431/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4862039961248431547118066754550924465431/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1206 BracketBatch0075.bracket1207 (4862039961248431547118066754550924465431/5000000000000000000000000000000000000000) (225726655624746824478435268986401673471/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1206 BracketBatch0075.bracket1207
  (4862039961248431547118066754550924465431/5000000000000000000000000000000000000000) (225726655624746824478435268986401673471/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1206
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1207
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (2434654785685545118202534776499863575371/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2434654785685545118202534776499863575371/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0188.rows BesselBatch0188.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (4883919536177236375267589577908253666553/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4883919536177236375267589577908253666553/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0583.rows BesselBatch0583.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (1950645821509665322334531826181596163459/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1950645821509665322334531826181596163459/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0150.rows ScalarLogs0150.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0075.bracket1207 BracketBatch0075.bracket1208 (1950645821509665322334531826181596163459/2000000000000000000000000000000000000000) (56823393468074821471838279525414927909/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0075.bracket1207 BracketBatch0075.bracket1208
  (1950645821509665322334531826181596163459/2000000000000000000000000000000000000000) (56823393468074821471838279525414927909/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1207
