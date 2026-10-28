module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Persistence of finitely many contacts under a small perturbation

The statements here are independent of polynomial approximation.  They isolate
the elementary analytic argument that turns a finite, signed contact
certificate into a bound on the entire interval.  In particular, no assertion
that a candidate polynomial is a best approximant is assumed in this file.
-/

namespace Lorentz
namespace Stability

/-- Multiplication by either of the two real signs does not change absolute
value. -/
lemma abs_sign_mul {s y : ℝ} (hs : s = 1 ∨ s = -1) : |s * y| = |y| := by
  rcases hs with rfl | rfl <;> simp

/-- A signed real value is bounded above by its absolute value. -/
lemma sign_mul_le_abs {s y : ℝ} (hs : s = 1 ∨ s = -1) : s * y ≤ |y| := by
  calc
    s * y ≤ |s * y| := le_abs_self _
    _ = |y| := abs_sign_mul hs

/-- A signed gap and a contact Lipschitz bound absorb a perturbation with one
smallness condition. No assumption on the sign of the perturbed value is needed. -/
theorem signed_contact_persistence_at
    {b r : ℝ → ℝ} {x z s E c L ell ε : ℝ}
    (hs : s = 1 ∨ s = -1) (hε : 0 ≤ ε)
    (hgap : c * |x - z| ≤ E - s * b x)
    (hlip : |r x - r z| ≤ L * |x - z|)
    (hcontact : s * r z ≤ ell) (hsmall : ε * L ≤ c) :
    s * (b x + ε * r x) ≤ E + ε * ell := by
  have hdiff := (sign_mul_le_abs hs).trans hlip
  have hscaled := mul_le_mul_of_nonneg_left hdiff hε
  have hcontact' := mul_le_mul_of_nonneg_left hcontact hε
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (abs_nonneg (x - z))
  nlinarith

/-- Apply the signed estimate twice, using a contact of each prescribed sign.
The gap may use different contacts for the two signs. -/
theorem signed_contact_persistence_bound
    {K : Set ℝ} {b r : ℝ → ℝ} {E c L ell ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε * L ≤ c)
    (hcover : ∀ x ∈ K, ∀ s : ℝ, s = 1 ∨ s = -1 → ∃ z : ℝ,
      c * |x - z| ≤ E - s * b x ∧
      |r x - r z| ≤ L * |x - z| ∧ s * r z ≤ ell) :
    ∀ x ∈ K, |b x + ε * r x| ≤ E + ε * ell := by
  intro x hx
  have upper (s : ℝ) (hs : s = 1 ∨ s = -1) :
      s * (b x + ε * r x) ≤ E + ε * ell := by
    obtain ⟨z, hgap, hlip, hcontact⟩ := hcover x hx s hs
    exact signed_contact_persistence_at hs hε hgap hlip hcontact hsmall
  have hp := upper 1 (Or.inl rfl)
  have hm := upper (-1) (Or.inr rfl)
  rw [abs_le]
  constructor <;> linarith

/-- The elementary pointwise step of contact persistence.

The point `z` is a contact used to control `x`.  The loss in the unperturbed
residual is at least `c * |x-z|`.  Nearby, the signed unperturbed residual is
positive and the perturbation is Lipschitz relative to the contact.  Far away,
the uniform bound `R` and the gap absorb the perturbation. -/
theorem contact_persistence_at
    {b r : ℝ → ℝ} {x z s E c δ L R ell ε : ℝ}
    (hs : s = 1 ∨ s = -1)
    (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hgap : c * |x - z| ≤ E - |b x|)
    (hlocal : |x - z| ≤ δ →
      E / 2 ≤ s * b x ∧ |r x - r z| ≤ L * |x - z|)
    (hcontact : s * r z ≤ ell)
    (hr : |r x| ≤ R)
    (hsmallLip : ε * L ≤ c)
    (hsmallSign : ε * R ≤ E / 2)
    (hsmallFar : ε * (R - ell) ≤ c * δ) :
    |b x + ε * r x| ≤ E + ε * ell := by
  by_cases hnear : |x - z| ≤ δ
  · obtain ⟨hb, hlip⟩ := hlocal hnear
    have hrs : |s * r x| ≤ R := by
      rw [abs_sign_mul hs]
      exact hr
    have hrlo : -R ≤ s * r x := (abs_le.mp hrs).1
    have hrscaled := mul_le_mul_of_nonneg_left hrlo hε
    have hnonneg : 0 ≤ s * (b x + ε * r x) := by
      nlinarith
    have hrupper : s * r x ≤ ell + L * |x - z| := by
      have hdiff : s * (r x - r z) ≤ L * |x - z| :=
        (sign_mul_le_abs hs).trans hlip
      nlinarith
    have hscaledLip :=
      mul_le_mul_of_nonneg_right hsmallLip (abs_nonneg (x - z))
    calc
      |b x + ε * r x| = |s * (b x + ε * r x)| :=
        (abs_sign_mul hs).symm
      _ = s * (b x + ε * r x) := abs_of_nonneg hnonneg
      _ = s * b x + ε * (s * r x) := by ring
      _ ≤ |b x| + ε * (ell + L * |x - z|) :=
        add_le_add (sign_mul_le_abs hs)
          (mul_le_mul_of_nonneg_left hrupper hε)
      _ ≤ E + ε * ell := by nlinarith
  · have hfar : δ ≤ |x - z| := le_of_lt (lt_of_not_ge hnear)
    have hscaledFar := mul_le_mul_of_nonneg_left hfar hc
    calc
      |b x + ε * r x| ≤ |b x| + |ε * r x| := abs_add_le _ _
      _ = |b x| + ε * |r x| := by
        rw [abs_mul, abs_of_nonneg hε]
      _ ≤ |b x| + ε * R :=
        add_le_add_right (mul_le_mul_of_nonneg_left hr hε) _
      _ ≤ E + ε * ell := by nlinarith

/-- A contact-persistence theorem on an arbitrary set.

The witness hypothesis `hcover` is a convenient topology-free way of saying
that the global linear gap is measured from a nearest contact.  It is enough
to supply any contact with this gap; the next theorem gives the usual finite
nearest-contact adapter. -/
theorem contact_persistence_bound
    {K S : Set ℝ} {b r σ : ℝ → ℝ} {E c δ L R ell ε : ℝ}
    (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hsign : ∀ z ∈ S, σ z = 1 ∨ σ z = -1)
    (hcover : ∀ x ∈ K, ∃ z ∈ S, c * |x - z| ≤ E - |b x|)
    (hlocal : ∀ x ∈ K, ∀ z ∈ S, |x - z| ≤ δ →
      E / 2 ≤ σ z * b x ∧ |r x - r z| ≤ L * |x - z|)
    (hcontact : ∀ z ∈ S, σ z * r z ≤ ell)
    (hr : ∀ x ∈ K, |r x| ≤ R)
    (hsmallLip : ε * L ≤ c)
    (hsmallSign : ε * R ≤ E / 2)
    (hsmallFar : ε * (R - ell) ≤ c * δ) :
    ∀ x ∈ K, |b x + ε * r x| ≤ E + ε * ell := by
  intro x hx
  obtain ⟨z, hz, hgap⟩ := hcover x hx
  exact contact_persistence_at (hsign z hz) hε hc hgap
    (hlocal x hx z hz) (hcontact z hz) (hr x hx)
    hsmallLip hsmallSign hsmallFar

/-- A nonempty finite set contains a contact nearest to any specified point. -/
theorem exists_nearest_contact (S : Finset ℝ) (hS : S.Nonempty) (x : ℝ) :
    ∃ z ∈ S, ∀ w ∈ S, |x - z| ≤ |x - w| := by
  exact Finset.exists_min_image S (fun z => |x - z|) hS

/-- The finite-contact version of `contact_persistence_bound`.  The linear
gap needs to be checked only for nearest contacts. -/
theorem finite_contact_persistence_bound
    {K : Set ℝ} {S : Finset ℝ} {b r σ : ℝ → ℝ} {E c δ L R ell ε : ℝ}
    (hS : S.Nonempty)
    (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hsign : ∀ z ∈ S, σ z = 1 ∨ σ z = -1)
    (hgap : ∀ x ∈ K, ∀ z ∈ S,
      (∀ w ∈ S, |x - z| ≤ |x - w|) → c * |x - z| ≤ E - |b x|)
    (hlocal : ∀ x ∈ K, ∀ z ∈ S, |x - z| ≤ δ →
      E / 2 ≤ σ z * b x ∧ |r x - r z| ≤ L * |x - z|)
    (hcontact : ∀ z ∈ S, σ z * r z ≤ ell)
    (hr : ∀ x ∈ K, |r x| ≤ R)
    (hsmallLip : ε * L ≤ c)
    (hsmallSign : ε * R ≤ E / 2)
    (hsmallFar : ε * (R - ell) ≤ c * δ) :
    ∀ x ∈ K, |b x + ε * r x| ≤ E + ε * ell := by
  apply contact_persistence_bound hε hc hsign
  · intro x hx
    obtain ⟨z, hz, hnearest⟩ := exists_nearest_contact S hS x
    exact ⟨z, hz, hgap x hx z hz hnearest⟩
  · exact hlocal
  · exact hcontact
  · exact hr
  · exact hsmallLip
  · exact hsmallSign
  · exact hsmallFar

/-- Signed equality at a contact persists with the correspondingly changed
error level.  No inequalities or regularity assumptions are needed here. -/
theorem contact_equality
    {b r s E ell ε : ℝ}
    (hs : s = 1 ∨ s = -1)
    (hb : b = s * E) (hr : s * r = ell) :
    b + ε * r = s * (E + ε * ell) := by
  have hss : s * s = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hr' : r = s * ell := by
    calc
      r = (s * s) * r := by rw [hss]; ring
      _ = s * (s * r) := by ring
      _ = s * ell := by rw [hr]
  rw [hb, hr']
  ring

/-- A contact equality also gives equality of absolute values when the new
error level is nonnegative. -/
theorem contact_abs_equality
    {b r s E ell ε : ℝ}
    (hs : s = 1 ∨ s = -1)
    (hb : b = s * E) (hr : s * r = ell)
    (hlevel : 0 ≤ E + ε * ell) :
    |b + ε * r| = E + ε * ell := by
  rw [contact_equality hs hb hr, abs_sign_mul hs, abs_of_nonneg hlevel]

/-- The explicit conservative constants used in the Lorentz construction.
All numerical smallness conditions are discharged in this theorem. -/
theorem contact_persistence_bound_explicit
    {K S : Set ℝ} {b r σ : ℝ → ℝ} {E ell : ℝ}
    (hE : (1 : ℝ) / 3 ≤ E) (hell : -20 ≤ ell)
    (hsign : ∀ z ∈ S, σ z = 1 ∨ σ z = -1)
    (hcover : ∀ x ∈ K, ∃ z ∈ S,
      (1 : ℝ) / 250 * |x - z| ≤ E - |b x|)
    (hlocal : ∀ x ∈ K, ∀ z ∈ S, |x - z| ≤ (1 : ℝ) / 1000 →
      E / 2 ≤ σ z * b x ∧ |r x - r z| ≤ 100000 * |x - z|)
    (hcontact : ∀ z ∈ S, σ z * r z ≤ ell)
    (hr : ∀ x ∈ K, |r x| ≤ 20) :
    ∀ x ∈ K,
      |b x + ((1 : ℝ) / 10000000000) * r x| ≤
        E + ((1 : ℝ) / 10000000000) * ell := by
  apply contact_persistence_bound (by norm_num) (by norm_num)
    hsign hcover hlocal hcontact hr
  · norm_num
  · nlinarith
  · nlinarith

/-- Positive gap, neighborhood radius, and baseline error admit a common
positive perturbation threshold, without requiring explicit numerical
estimates.  The threshold controls every error correction with magnitude at
most `R`, and every baseline error at least `Emin`. -/
theorem exists_uniform_small_parameter
    {Emin c δ L R : ℝ}
    (hE : 0 < Emin) (hc : 0 < c) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hR : 0 ≤ R) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      ε * L ≤ c ∧ ε * R ≤ Emin / 2 ∧
      2 * ε * R ≤ c * δ ∧ ε * R < Emin := by
  let A : ℝ := min c (min (Emin / 4) (c * δ))
  let M : ℝ := L + 2 * R + 1
  have hA : 0 < A := by
    dsimp [A]
    exact lt_min hc (lt_min (by positivity) (mul_pos hc hδ))
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨A / M, div_pos hA hM, ?_⟩
  intro ε hε hsmall
  have hεM : ε * M ≤ A := (le_div_iff₀ hM).1 hsmall
  have hAc : A ≤ c := min_le_left _ _
  have hAE : A ≤ Emin / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hAδ : A ≤ c * δ := (min_le_right _ _).trans (min_le_right _ _)
  have hML : L ≤ M := by dsimp [M]; linarith
  have hMR : R ≤ M := by dsimp [M]; linarith
  have hM2R : 2 * R ≤ M := by dsimp [M]; linarith
  have hεL := mul_le_mul_of_nonneg_left hML hε
  have hεR := mul_le_mul_of_nonneg_left hMR hε
  have hε2R := mul_le_mul_of_nonneg_left hM2R hε
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The qualitative finite-contact persistence theorem: a single positive
threshold works for every smaller nonnegative perturbation. -/
theorem exists_contact_persistence_threshold
    {K S : Set ℝ} {b r σ : ℝ → ℝ} {E Emin c δ L R ell : ℝ}
    (hEmin : 0 < Emin) (hE : Emin ≤ E)
    (hc : 0 < c) (hδ : 0 < δ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hell : |ell| ≤ R)
    (hsign : ∀ z ∈ S, σ z = 1 ∨ σ z = -1)
    (hcover : ∀ x ∈ K, ∃ z ∈ S, c * |x - z| ≤ E - |b x|)
    (hlocal : ∀ x ∈ K, ∀ z ∈ S, |x - z| ≤ δ →
      E / 2 ≤ σ z * b x ∧ |r x - r z| ≤ L * |x - z|)
    (hcontact : ∀ z ∈ S, σ z * r z ≤ ell)
    (hr : ∀ x ∈ K, |r x| ≤ R) :
    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →
      0 < E + ε * ell ∧
      ∀ x ∈ K, |b x + ε * r x| ≤ E + ε * ell := by
  obtain ⟨ε₀, hε₀, hthreshold⟩ := exists_uniform_small_parameter hEmin hc hδ hL hR
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨hsmallLip, hsmallSign, hsmallFar, hpositive⟩ := hthreshold ε hε hsmall
  have helllo : -R ≤ ell := (abs_le.mp hell).1
  have hscaled := mul_le_mul_of_nonneg_left helllo hε
  constructor
  · nlinarith
  · apply contact_persistence_bound hε hc.le hsign hcover hlocal hcontact hr
      hsmallLip
    · linarith
    · nlinarith

end Stability
end Lorentz
