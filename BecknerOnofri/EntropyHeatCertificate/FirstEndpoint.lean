import BecknerOnofri.EntropyHeatPanelCertificate
import BecknerOnofri.EntropyHeatCertificate.Exp0000
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
def firstChunk : CheckedChunk := ⟨Exp0000.entries, Exp0000.accepted⟩
def firstEndpoint : SmallEndpoint := ⟨9950248756218905472636815920/10^30, 990593802343360973667885776181584566130326199/10^30,
  firstChunk.entries[0]'(by decide), firstChunk.entries[1]'(by decide)⟩
theorem firstEndpoint_checked : firstEndpoint.check = true := by decide +kernel
theorem firstEndpoint_bound :
    heatComplement (9950248756218905472636815920/10^30 : ℝ) ≤ 990593802343360973667885776181584566130326199/10^30 := by
  have h := SmallEndpoint.sound firstEndpoint firstEndpoint_checked
    (firstChunk.valid ⟨0, by decide⟩) (firstChunk.valid ⟨1, by decide⟩)
  simpa only [firstEndpoint, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h
#print axioms firstEndpoint_bound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
