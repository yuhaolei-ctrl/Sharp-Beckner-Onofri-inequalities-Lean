module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0072
public import BecknerOnofri.EntropyScalarCertificate.Bessel0073
public import BecknerOnofri.EntropyScalarCertificate.Bessel0525
public import BecknerOnofri.EntropyScalarCertificate.Brackets0029
public import BecknerOnofri.EntropyScalarCertificate.Logs0058
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0464
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (11796528421757289526168418127128506331/78125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11796528421757289526168418127128506331/78125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (151202473835302707812085072429732993957/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (151202473835302707812085072429732993957/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1510990188168980068735204122284889374969/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1510990188168980068735204122284889374969/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0464 BracketBatch0029.bracket0465 (1510990188168980068735204122284889374969/10000000000000000000000000000000000000000) (390169554688037132558375747093932943/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0464 BracketBatch0029.bracket0465
  (1510990188168980068735204122284889374969/10000000000000000000000000000000000000000) (390169554688037132558375747093932943/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0464
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0465
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1512024738353027078120850724297329939567/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1512024738353027078120850724297329939567/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (18926175372192763270920579445394039147/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18926175372192763270920579445394039147/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (3026118768128448139794497079928853071327/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3026118768128448139794497079928853071327/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0465 BracketBatch0029.bracket0466 (3026118768128448139794497079928853071327/20000000000000000000000000000000000000000) (392276192833605970831829851007573511/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0465 BracketBatch0029.bracket0466
  (3026118768128448139794497079928853071327/20000000000000000000000000000000000000000) (392276192833605970831829851007573511/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0465
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0466
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1514094029775421061673646355631523131757/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1514094029775421061673646355631523131757/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (379040878135098541942109852018018478539/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (379040878135098541942109852018018478539/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (3030257542315815229442085763703597045913/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3030257542315815229442085763703597045913/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0466 BracketBatch0029.bracket0467 (3030257542315815229442085763703597045913/20000000000000000000000000000000000000000) (39439138042709019872288220216600937/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0466 BracketBatch0029.bracket0467
  (3030257542315815229442085763703597045913/20000000000000000000000000000000000000000) (39439138042709019872288220216600937/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0466
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0467
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0072.rows BesselBatch0072.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1516163512540394167768439408072073914153/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1516163512540394167768439408072073914153/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1518233186936364698685837783161451707727/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1518233186936364698685837783161451707727/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (75859917486918971661356929780838140547/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (75859917486918971661356929780838140547/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0467 BracketBatch0029.bracket0468 (75859917486918971661356929780838140547/500000000000000000000000000000000000000) (396515140885372875200549207776058807/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0467 BracketBatch0029.bracket0468
  (75859917486918971661356929780838140547/500000000000000000000000000000000000000) (396515140885372875200549207776058807/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0467
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0468
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (379558296734091174671459445790362926931/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (379558296734091174671459445790362926931/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (304060610650378068682169171921769155917/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (304060610650378068682169171921769155917/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (3038536240188255042096683642770297487309/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3038536240188255042096683642770297487309/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0468 BracketBatch0029.bracket0469 (3038536240188255042096683642770297487309/20000000000000000000000000000000000000000) (19932374882976540832051642579424239/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0468 BracketBatch0029.bracket0469
  (3038536240188255042096683642770297487309/20000000000000000000000000000000000000000) (19932374882976540832051642579424239/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0468
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0469
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (760151526625945171705422929804422889791/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (760151526625945171705422929804422889791/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (761186555887834210033772166394050269977/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (761186555887834210033772166394050269977/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (190167260314222422717399387024809144971/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (190167260314222422717399387024809144971/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0469 BracketBatch0029.bracket0470 (190167260314222422717399387024809144971/1250000000000000000000000000000000000000) (40078847423484675212096203670812457/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0469 BracketBatch0029.bracket0470
  (190167260314222422717399387024809144971/1250000000000000000000000000000000000000) (40078847423484675212096203670812457/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0469
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0470
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (1522373111775668420067544332788100539951/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1522373111775668420067544332788100539951/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (190555420349567014825584912253124081241/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (190555420349567014825584912253124081241/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (3046816474572204538672223630813093189879/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3046816474572204538672223630813093189879/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0470 BracketBatch0029.bracket0471 (3046816474572204538672223630813093189879/20000000000000000000000000000000000000000) (20146904706541074950343559814622069/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0470 BracketBatch0029.bracket0471
  (3046816474572204538672223630813093189879/20000000000000000000000000000000000000000) (20146904706541074950343559814622069/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0470
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0471
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (60977734511861444744187171920999705997/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (60977734511861444744187171920999705997/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1526513806603470743732674390069343892443/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1526513806603470743732674390069343892443/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (95342411543750214448042302752948016949/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (95342411543750214448042302752948016949/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0058.rows ScalarLogs0058.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0471 BracketBatch0029.bracket0472 (95342411543750214448042302752948016949/625000000000000000000000000000000000000) (405096380901186158859016402857311651/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0471 BracketBatch0029.bracket0472
  (95342411543750214448042302752948016949/625000000000000000000000000000000000000) (405096380901186158859016402857311651/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0471
