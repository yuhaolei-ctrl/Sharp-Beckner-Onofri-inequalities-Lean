import BecknerOnofri.Friedrichs.MixedAngularOperator

/-! Actual mixed spatial operator eigenvectors used in the finite cosine-sum
step of the manuscript. The coordinate frequency may be less than alpha. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Polynomial
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial
open Legacy.BecknerOnofri.JacobiAngular

 def chebyshevProfiles {d : ℕ} (α n : MultiIndex d) (i : Fin d) (z : ℝ) : ℝ :=
  (derivative^[α i] (Chebyshev.T ℝ (n i : ℤ))).eval z

lemma chebyshevProfiles_smooth {d : ℕ} (α n : MultiIndex d) (i : Fin d) :
    ContDiff ℝ ∞ (chebyshevProfiles α n i) := polynomial_contDiff _

lemma angularImage_chebyshev (m n : ℕ) (t : ℝ) :
    angularImage m (fun z => (derivative^[m] (Chebyshev.T ℝ (n:ℤ))).eval z) t=
      (n:ℝ)^2*angular m (fun z => (derivative^[m] (Chebyshev.T ℝ (n:ℤ))).eval z) t := by
  let p := derivative^[m] (Chebyshev.T ℝ (n:ℤ))
  have he := congrArg (fun q : Polynomial ℝ => q.eval (Real.cos t))
    (Legacy.BecknerOnofri.JacobiPolynomial.shifted_chebyshev_derivative (n:ℤ) m)
  have hs : (Legacy.BecknerOnofri.JacobiPolynomial.shifted m p).eval (Real.cos t)=
      (n:ℝ)^2*p.eval (Real.cos t) := by simpa [p] using he
  change Real.sin t^m*(jacobi m (fun z => p.eval z) (Real.cos t)+(m:ℝ)^2*p.eval (Real.cos t))=_
  rw [jacobi_eval]
  have h := congrArg (fun y : ℝ => Real.sin t^m*y) hs
  simpa [Legacy.BecknerOnofri.JacobiPolynomial.shifted,angular,mul_comm,mul_left_comm,mul_assoc,p] using h

lemma angularOperatorImage_chebyshev {d : ℕ} (α n : MultiIndex d) (x : Space d) :
    angularOperatorImage α (chebyshevProfiles α n) x=
      (∑ i,(n i:ℝ)^2)*angularFunction α (chebyshevProfiles α n) x := by
  unfold angularOperatorImage
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  unfold angularCoordinateImage
  have hc : angularImage (α i) (chebyshevProfiles α n i) (x i)=
      (n i:ℝ)^2*angularProfiles α (chebyshevProfiles α n) i (x i) :=
    angularImage_chebyshev (α i) (n i) (x i)
  rw [hc]
  have hp := Finset.prod_erase_mul Finset.univ
    (fun j => angularProfiles α (chebyshevProfiles α n) j (x j)) (Finset.mem_univ i)
  change (∏ j∈Finset.univ.erase i,angularProfiles α (chebyshevProfiles α n) j (x j))*
      ((n i:ℝ)^2*angularProfiles α (chebyshevProfiles α n) i (x i))=_
  rw [← mul_left_comm, hp]
  rfl

def chebyshevVector {d : ℕ} (α n : MultiIndex d) : H α :=
  (angularLift α (chebyshevProfiles α n) (chebyshevProfiles_smooth α n)).1

theorem chebyshevVector_operatorGraph {d : ℕ} (α n : MultiIndex d) :
    operatorGraph α (chebyshevVector α n) ((∑ i,(n i:ℝ)^2) • chebyshevVector α n) := by
  have h := angular_operatorGraph α (chebyshevProfiles α n) (chebyshevProfiles_smooth α n)
  have he : angularOperatorImageLp α (chebyshevProfiles α n) (chebyshevProfiles_smooth α n)=
      (∑ i,(n i:ℝ)^2) • chebyshevVector α n := by
    apply Lp.ext
    filter_upwards [(continuous_memLp α (angularOperatorImage_continuous α
      (chebyshevProfiles α n) (chebyshevProfiles_smooth α n))).coeFn_toLp,
      Lp.coeFn_smul (∑ i,(n i:ℝ)^2) (chebyshevVector α n),
      (angular_memLp α (chebyshevProfiles α n) (chebyshevProfiles_smooth α n)).coeFn_toLp] with x hx hs hv
    change angularOperatorImageLp α (chebyshevProfiles α n) (chebyshevProfiles_smooth α n) x=
      angularOperatorImage α (chebyshevProfiles α n) x at hx
    change chebyshevVector α n x=angularFunction α (chebyshevProfiles α n) x at hv
    rw [hx,hs]
    simpa only [Pi.smul_apply,smul_eq_mul,hv] using angularOperatorImage_chebyshev α n x
  rw [he] at h
  exact h

#print axioms chebyshevVector_operatorGraph
end BecknerOnofri.Friedrichs.MixedSpatial
