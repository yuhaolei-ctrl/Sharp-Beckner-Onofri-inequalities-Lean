import BecknerOnofri.ArcsineConvolution

/-! The entire exterior radial-bin integral bound, with the precise bins that
cross S=1 included and probabilities given by the true arcsine convolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ArcsineProductBins

theorem lower_endpoint_mem {N d : ℕ} (hN : 0<N) (hdN : d≤N) (b : Fin d → Fin N)
    (hb : N-d+1 ≤ indexSum b) : (indexSum b:ℝ)/N∈Ioc (0:ℝ) d := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hj : 0 < indexSum b := by omega
  refine ⟨div_pos (Nat.cast_pos.mpr hj) hNr,(div_le_iff₀ hNr).mpr ?_⟩
  have hh := (indexSum_le b).trans (Nat.mul_le_mul_left d (Nat.sub_le N 1))
  exact_mod_cast hh

/-- A valid coefficientwise bound on each cell bounds the whole exterior integral. -/
theorem exterior_integral_cell_bound {N d : ℕ} (hN : 0<N) (hd : 0<d) (hdN : d≤N)
    (f : Torus d → ℝ) (hf : Integrable f (torusMeasure d)) (B : (Fin d → Fin N) → ℝ)
    (hB0 : ∀ b,0≤B b) (hB : ∀ b x,x∈cell b → 1<radialSum x → f x≤B b) :
    (∫ x in {x : Torus d | 1<radialSum x}, f x ∂torusMeasure d)≤
      ∑ b : Fin d → Fin N,cellMass b*B b := by
  classical
  let E : Set (Torus d) := {x | 1<radialSum x}
  have hE : MeasurableSet E := (radialSum_continuous d).measurable measurableSet_Ioi
  let g := E.indicator f
  have hg : Integrable g (torusMeasure d) := hf.indicator hE
  have hcover : ∀ᵐ x ∂torusMeasure d,x∈⋃ b : Fin d → Fin N,cell b := by
    filter_upwards [cells_cover_ae (d:=d) hN] with x hx
    exact Set.mem_iUnion.mpr hx
  rw [← integral_indicator hE]
  change (∫ x,g x ∂torusMeasure d)≤_
  rw [integral_eq_setIntegral hcover g,integral_iUnion_fintype (cell_measurable)
    (fun _ _ hab => cells_disjoint hN hab) (fun b => hg.integrableOn)]
  apply Finset.sum_le_sum
  intro b _
  have hh : (∫ x in cell b,g x ∂torusMeasure d)≤∫ _x in cell b,B b ∂torusMeasure d := by
    apply setIntegral_mono_on hg.integrableOn (integrable_const (B b)) (cell_measurable b)
    intro x hx
    by_cases hS : 1<radialSum x
    · simpa [g,E,Set.indicator_of_mem,hS] using hB b x hx hS
    · simpa [g,E,Set.indicator_of_notMem,hS] using hB0 b
  simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,cell_measure hN] using hh

/-- Source exterior-bin bound: the exact profile is antitone; its enclosure need not be. -/
theorem exterior_integral_bound {N d : ℕ} (hN : 0<N) (hd : 0<d) (hdN : d≤N)
    (f : Torus d → ℝ) (hf : Integrable f (torusMeasure d)) (K R : ℝ → ℝ)
    (hK : AntitoneOn K (Ioc (0:ℝ) d))
    (hfK : ∀ x,1<radialSum x → f x≤Real.exp ((7/10:ℝ)*K (radialSum x)))
    (hR : ∀ S∈Ioc (0:ℝ) d,K S≤R S) :
    (∫ x in {x : Torus d | 1<radialSum x}, f x ∂torusMeasure d)≤
      ∑ j∈Finset.range (d*(N-1)+1),if N-d+1 ≤ j then
        convolution N d j*Real.exp ((7/10:ℝ)*R ((j:ℝ)/N)) else 0 := by
  classical
  let w : ℕ → ℝ := fun j => if N-d+1 ≤ j then Real.exp ((7/10:ℝ)*R ((j:ℝ)/N)) else 0
  have hmain := exterior_integral_cell_bound hN hd hdN f hf (fun b => w (indexSum b))
    (fun b => by dsimp [w]; split_ifs <;> positivity) (by
      intro b x hx hS
      have hj := cell_crossing_index hN hd hdN hx hS
      simp only [w,if_pos hj]
      have hsmall := lower_endpoint_mem hN hdN b hj
      have hlarge : radialSum x∈Ioc (0:ℝ) d := ⟨by linarith,(radialSum_mem x).2⟩
      apply (hfK x hS).trans
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤7/10)
      exact (hK hsmall hlarge (cell_location hN hd hx).1).trans (hR _ hsmall))
  rw [sum_cell_weight_eq] at hmain
  convert! hmain using 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp [w]
  split_ifs <;> simp

/-- The exact finite exterior expression used in the dimension-twelve source. -/
theorem source_exterior_integral_bound (f : Torus 12 → ℝ) (hf : Integrable f (torusMeasure 12))
    (K R : ℝ → ℝ) (hK : AntitoneOn K (Ioc (0:ℝ) 12))
    (hfK : ∀ x,1<radialSum x → f x≤Real.exp ((7/10:ℝ)*K (radialSum x)))
    (hR : ∀ S∈Ioc (0:ℝ) 12,K S≤R S) :
    (∫ x in {x : Torus 12 | 1<radialSum x}, f x ∂torusMeasure 12)≤
      ∑ j∈Finset.range 49141,if 4085 ≤ j then
        convolution 4096 12 j*Real.exp ((7/10:ℝ)*R ((j:ℝ)/4096)) else 0 := by
  simpa only [Nat.cast_ofNat,show (12:ℕ)*(4096-1)+1=49141 by norm_num,show (4096:ℕ)-12+1=4085 by norm_num] using
    exterior_integral_bound (N:=4096) (d:=12) (by norm_num) (by norm_num) (by norm_num) f hf K R hK hfK hR

#print axioms exterior_integral_cell_bound
#print axioms source_exterior_integral_bound
end BecknerOnofri.HighDim.ArcsineProductBins
