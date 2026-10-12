module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CosetIdealCorrespondence
public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels
public import DedekindZetaZeroFree.LFunctions.Dedekind.IdealNormSeries

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable {K : Type} [Field K] [NumberField K]

def signedOrbitWeight (D : Data K) (δ : Finset (RealPlaces K)) (s : ℂ)
    (x : X D) : ℂ :=
  (signδ D δ x : ℂ) * (normWeight D x : ℂ) ^ (-s)

def Zδ (D : Data K) (δ : Finset (RealPlaces K)) (s : ℂ) : ℂ :=
  ∑' x : X D, signedOrbitWeight D δ s x

theorem normWeight_pos (D : Data K) (x : X D) :
    0 < normWeight D x := by
  induction x using Quotient.inductionOn with
  | h α =>
    show 0 < normWeight D (orbitMk D α)
    rw [normWeight_orbitMk]
    unfold representativeNormWeight
    apply div_pos
    · rw [abs_pos]
      have hα : (α.val : K) ≠ 0 :=
        NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
          ((mem_Cnonzero_iff D α.val).mp α.property).2
      exact_mod_cast (Algebra.norm_eq_zero_iff.not.mpr hα)
    · exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot)

theorem norm_signδ (D : Data K) (δ : Finset (RealPlaces K)) (x : X D) :
    ‖(signδ D δ x : ℂ)‖ = 1 := by
  induction x using Quotient.inductionOn with
  | h α =>
    show ‖(signδ D δ (orbitMk D α) : ℂ)‖ = 1
    rw [signδ_orbitMk]
    have hα : (α.val : K) ≠ 0 :=
      NumberField.RingOfIntegers.coe_ne_zero_iff.mpr
        ((mem_Cnonzero_iff D α.val).mp α.property).2
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold representativeSign
    rw [Finset.abs_prod]
    apply Finset.prod_eq_one
    intro v _
    have hne : realEmbedding K v (α.val : K) ≠ 0 :=
      fun h => hα (RingHom.injective (realEmbedding K v) (by simpa using h))
    rcases Real.sign_apply_eq_of_ne_zero _ hne with h | h <;> rw [h] <;> norm_num

 def orbitSignEmbedding (D : Data K) :
    X D ↪ Ideal (𝓞 K) × RealSignVector K where
  toFun x := (orbitIdeal D x, signVector D x)
  inj' := by
    intro x y h
    have hI : orbitIdeal D x = orbitIdeal D y := congrArg Prod.fst h
    have hs : signVector D x = signVector D y := congrArg Prod.snd h
    let a : {z : X D // orbitIdeal D z = orbitIdeal D x} := ⟨x, rfl⟩
    let b : {z : X D // orbitIdeal D z = orbitIdeal D x} := ⟨y, hI.symm⟩
    have hab : a = b :=
      signVector_injective_on_fibre D (orbitIdeal D x) (by simpa [a, b] using hs)
    simpa [a, b] using congrArg Subtype.val hab

theorem summable_normWeight_rpow (D : Data K) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun x : X D => (normWeight D x : ℝ) ^ (-s.re)) := by
  have hF : Summable (fun p : Ideal (𝓞 K) × RealSignVector K =>
      (Ideal.absNorm p.1 : ℝ) ^ (-s.re)) := by
    have h1 : Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-s.re)) :=
      DedekindZetaZeroFree.Odlyzko.summable_ideal_absNorm_rpow K hs
    have h2 : Summable (fun _ : RealSignVector K => (1 : ℝ)) := Summable.of_finite
    have h3 := h1.mul_of_nonneg h2 (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun _ => zero_le_one)
    simpa using h3
  apply (hF.comp_injective (orbitSignEmbedding D).injective).congr
  intro x
  show (Ideal.absNorm (orbitIdeal D x) : ℝ) ^ (-s.re) = _
  rw [orbitIdeal_absNorm]

theorem summable_norm_signedOrbitWeight (D : Data K)
    (δ : Finset (RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun x : X D => ‖signedOrbitWeight D δ s x‖) := by
  apply (summable_normWeight_rpow D s hs).congr
  intro x
  rw [signedOrbitWeight, norm_mul, norm_signδ D δ x, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (normWeight_pos D x) (-s), Complex.neg_re]

theorem summable_signedOrbitWeight (D : Data K)
    (δ : Finset (RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    Summable (signedOrbitWeight D δ s) :=
  (summable_norm_signedOrbitWeight D δ s hs).of_norm

theorem hasSum_signedOrbitWeight (D : Data K)
    (δ : Finset (RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    HasSum (signedOrbitWeight D δ s) (Zδ D δ s) :=
  (summable_signedOrbitWeight D δ s hs).hasSum

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
