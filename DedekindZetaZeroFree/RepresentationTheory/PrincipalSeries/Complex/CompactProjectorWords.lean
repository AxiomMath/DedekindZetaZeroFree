module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarmonicPolynomials.CompactGenerator
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SphericalWordHarmonicBand
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.NormalizedPauliFlows
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.CompactHarmonicEigenvalues

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

open MeasureTheory

namespace CompactInterpolation

set_option backward.isDefEq.respectTransparency false

open KPCplxCharacterHaar KPCplxHarmonicIntertwinerSpectrum
open KPCplxHarmonicExtraction
open scoped BigOperators

private theorem restriction_bridge : polynomialCompactRestriction =
    KPCplxIntertwinerEigenvalues.polynomialCompactRestriction := rfl

def eigenvalue (m : ℕ) : ℂ := 2 * (m : ℂ) * ((m : ℂ) + 1)

private theorem eigenvalue_injective : Function.Injective eigenvalue := by
  intro m n he
  have hr := congrArg Complex.re he
  norm_num [eigenvalue, Complex.mul_re, Complex.mul_im] at hr
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have heq : (m : ℝ) = n := by nlinarith
  exact_mod_cast heq

def projectorPolynomial (N ℓ : ℕ) : Polynomial ℂ :=
  if ℓ ≤ N then Lagrange.basis (Finset.range (N + 1)) eigenvalue ℓ else 0

theorem projectorPolynomial_eval (N ℓ m : ℕ) (hm : m ≤ N) :
    (projectorPolynomial N ℓ).eval (eigenvalue m) = if m = ℓ then 1 else 0 := by
  classical
  by_cases hℓ : ℓ ≤ N
  · simp only [projectorPolynomial, if_pos hℓ]
    by_cases he : m = ℓ
    · subst m
      rw [Lagrange.eval_basis_self eigenvalue_injective.injOn
        (Finset.mem_range.mpr (by omega)), if_pos rfl]
    · rw [Lagrange.eval_basis_of_ne (Ne.symm he) (Finset.mem_range.mpr (by omega)),
        if_neg he]
  · have he : m ≠ ℓ := by omega
    simp [projectorPolynomial, hℓ, he]

def compactGeneratorEnd (j : Fin 3) : Module.End ℂ HarmonicVendor.Polynomial where
  toFun := HarmonicVendor.A j
  map_add' := by
    intro p q
    simp only [HarmonicVendor.A, HarmonicVendor.L, map_add, MvPolynomial.smul_eq_C_mul]
    ring
  map_smul' := by
    intro c p
    simp only [HarmonicVendor.A, HarmonicVendor.L, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.pderiv_C_mul, RingHom.id_apply]
    ring

def pauliCasimir : Module.End ℂ HarmonicVendor.Polynomial :=
  -(∑ j : Fin 3, compactGeneratorEnd j * compactGeneratorEnd j)

private theorem pauliCasimir_apply (p : HarmonicVendor.Polynomial) :
    pauliCasimir p = -(∑ j : Fin 3, HarmonicVendor.A j (HarmonicVendor.A j p)) := by
  simp [pauliCasimir, compactGeneratorEnd, Module.End.mul_apply]

theorem projector_harmonic (N ℓ m : ℕ) (hm : m ≤ N)
    (p : HarmonicVendor.Polynomial) (hp : p ∈ harmonicPolynomials m) :
    (Polynomial.aeval pauliCasimir (projectorPolynomial N ℓ)) p =
      if m = ℓ then p else 0 := by
  have he : pauliCasimir p = eigenvalue m • p := by
    rw [pauliCasimir_apply]
    exact HarmonicVendor.A_casimir_harmonic m ⟨p, hp⟩
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul he,
    projectorPolynomial_eval N ℓ m hm]
  split <;> simp_all

theorem character_eq_interpolation_harmonic
    (μ : Measure ComplexSU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (N ℓ m : ℕ) (hm : m ≤ N) (p : HarmonicVendor.Polynomial)
    (hp : p ∈ harmonicPolynomials m) (k : ComplexSU2) :
    (2 * ℓ + 1 : ℂ) *
      (∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
        polynomialCompactRestriction p (k * t) ∂μ) =
      polynomialCompactRestriction
        ((Polynomial.aeval pauliCasimir (projectorPolynomial N ℓ)) p) k := by
  rw [projector_harmonic N ℓ m hm p hp]
  simp_rw [restriction_bridge]
  by_cases he : m = ℓ
  · subst m
    simpa using CompactPolynomial.harmonic_character_projection_diagonal
      μ inferInstance inferInstance ℓ p hp k
  · rw [if_neg he, map_zero, Pi.zero_apply,
      CompactPolynomial.harmonic_character_projection_off_diagonal
        μ inferInstance inferInstance ℓ m he p hp k, mul_zero]

section FixedWords

variable {A : Type*} [Ring A] [Algebra ℂ A]

def compactWord (D : Fin 3 → A) (u : List (Fin 3)) : A :=
  u.foldr (fun j T => D j * T) 1

private theorem compactWord_append (D : Fin 3 → A)
    (u v : List (Fin 3)) : compactWord D (u ++ v) = compactWord D u * compactWord D v := by
  induction u with
  | nil => simp [compactWord]
  | cons j u ih =>
      simp only [compactWord, List.cons_append, List.foldr_cons] at *
      rw [ih, mul_assoc]

 def wordSpan (D : Fin 3 → A) : Submodule ℂ (A) :=
  Submodule.span ℂ (Set.range (compactWord D))

private theorem wordSpan_word (D : Fin 3 → A) (u : List (Fin 3)) :
    compactWord D u ∈ wordSpan D := Submodule.subset_span ⟨u, rfl⟩

private theorem wordSpan_mul (D : Fin 3 → A)
    {x y : A} (hx : x ∈ wordSpan D) (hy : y ∈ wordSpan D) :
    x * y ∈ wordSpan D := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨v, rfl⟩ := hy
          rw [← compactWord_append]
          exact wordSpan_word D _
      | zero => simpa using (wordSpan D).zero_mem
      | add x y hx hy ihx ihy =>
          rw [mul_add]
          exact (wordSpan D).add_mem ihx ihy
      | smul c x hx ih =>
          rw [mul_smul_comm]
          exact (wordSpan D).smul_mem c ih
  | zero => simpa using (wordSpan D).zero_mem
  | add x y hx hy ihx ihy =>
      rw [add_mul]
      exact (wordSpan D).add_mem ihx ihy
  | smul c x hx ih =>
      rw [smul_mul_assoc]
      exact (wordSpan D).smul_mem c ih

private theorem casimir_mem_wordSpan (D : Fin 3 → A) :
    -(∑ j : Fin 3, D j * D j) ∈ wordSpan D := by
  apply (wordSpan D).neg_mem
  apply (wordSpan D).sum_mem
  intro j hj
  simpa [compactWord] using wordSpan_word D [j, j]

theorem polynomial_compact_words (D : Fin 3 → A) (p : Polynomial ℂ) :
    ∃ (n : ℕ) (u : Fin n → List (Fin 3)) (c : Fin n → ℂ),
      Polynomial.aeval (-(∑ j : Fin 3, D j * D j)) p =
        ∑ j, c j • compactWord D (u j) := by
  classical
  let C := -(∑ j : Fin 3, D j * D j)
  have hC : C ∈ wordSpan D := casimir_mem_wordSpan D
  have hpow (a : ℕ) : C ^ a ∈ wordSpan D := by
    induction a with
    | zero => simpa [compactWord] using wordSpan_word D []
    | succ a ih => rw [pow_succ]; exact wordSpan_mul D ih hC
  have hp : Polynomial.aeval C p ∈ wordSpan D := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add]
        exact (wordSpan D).add_mem hp hq
    | monomial a c =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul]
        exact (wordSpan D).smul_mem c (hpow a)
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  let e := b.support.equivFin.symm
  refine ⟨b.support.card, fun j => (e j).val, fun j => b (e j).val, ?_⟩
  rw [← hb]
  change (∑ a ∈ b.support, b a • compactWord D a) = _
  rw [← Finset.sum_coe_sort b.support, ← e.sum_comp]

theorem universal_polynomial_compact_words (p : Polynomial ℂ) :
    ∃ (n : ℕ) (u : Fin n → List (Fin 3)) (c : Fin n → ℂ),
      ∀ {A : Type*} [Ring A] [Algebra ℂ A] (D : Fin 3 → A),
        Polynomial.aeval (-(∑ j : Fin 3, D j * D j)) p =
          ∑ j, c j • compactWord D (u j) := by
  obtain ⟨n, u, c, he⟩ := polynomial_compact_words (FreeAlgebra.ι ℂ : Fin 3 → FreeAlgebra ℂ (Fin 3)) p
  refine ⟨n, u, c, fun {A} _ _ D => ?_⟩
  let φ := FreeAlgebra.lift ℂ D
  have hι (j : Fin 3) : φ (FreeAlgebra.ι ℂ j) = D j := FreeAlgebra.lift_ι_apply D j
  have hword (v : List (Fin 3)) :
      φ (compactWord (FreeAlgebra.ι ℂ) v) = compactWord D v := by
    induction v with
    | nil => simp [compactWord]
    | cons j v ih =>
        simp only [compactWord, List.foldr_cons, map_mul, FreeAlgebra.lift_ι_apply] at *
        rw [ih, hι]
  have hh := congrArg φ he
  rw [← Polynomial.aeval_algHom_apply] at hh
  simpa only [map_neg, map_sum, map_mul, hι, map_smul, hword] using hh

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

variable {α : Type*}

end FixedWords

section ActualRealWords

open KPCplxPrincipalSeriesCharts KPContHolomorphicKGeneration

end ActualRealWords

end CompactInterpolation

namespace CompactOrbitProof
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPContHolomorphicKGeneration
open KPCplxIntertwinerEigenvalues
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem entire_eq_of_real {f h : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hh : AnalyticOnNhd ℂ h Set.univ)
    (he : ∀ t : ℝ, f t = h t) : f = h := by
  have hc : (0 : ℂ) ∈ closure ({z | f z = h z} \ {0}) := by
    apply mem_closure_of_tendsto
      (Complex.continuous_ofReal.tendsto 0 |>.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply Filter.Eventually.of_forall
    intro n
    refine ⟨he _, ?_⟩
    simp only [Set.mem_singleton_iff, Function.comp_apply, Complex.ofReal_eq_zero]
    positivity
  exact funext (fun z => hf.eqOn_of_preconnected_of_mem_closure hh
    isPreconnected_univ (Set.mem_univ 0) hc (Set.mem_univ z))

private theorem ratio_pos (g : ComplexGL2) : 0 < sphericalRatio g := by
  have hm := bottomRowMass_eq (g : Mat)
  have hb : 0 < bottomRowNormSq g := by
    by_contra h
    have hn : bottomRowNormSq g = 0 := le_antisymm (not_lt.mp h) (by
      unfold bottomRowNormSq; positivity)
    have h10 : (g : Mat) 1 0 = 0 := norm_eq_zero.mp (by
      dsimp [bottomRowNormSq] at hn
      nlinarith [norm_nonneg ((g : Mat) 1 0), norm_nonneg ((g : Mat) 1 1)])
    have h11 : (g : Mat) 1 1 = 0 := norm_eq_zero.mp (by
      dsimp [bottomRowNormSq] at hn
      nlinarith [norm_nonneg ((g : Mat) 1 0), norm_nonneg ((g : Mat) 1 1)])
    exact Matrix.GeneralLinearGroup.det_ne_zero g (by rw [Matrix.det_fin_two, h10, h11]; ring)
  exact div_pos (norm_pos_iff.mpr (Units.ne_zero _)) hb

private theorem spherical_real (t : ℝ) (g : ComplexGL2) :
    complexSpherical t g = sphericalSection (positiveParameter + t) g := by
  change Complex.exp (_ * (Real.log (sphericalRatio g) : ℂ)) =
    ((sphericalRatio g ^ (1 + 2 * (positiveParameter + t)) : ℝ) : ℂ)
  rw [Real.rpow_def_of_pos (ratio_pos g), Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private theorem word_real (w : RealLieWord) (t : ℝ) (g : ComplexGL2) :
    complexSphericalWord w t g =
      rightWord (positiveParameter + t) w (sphericalSection (positiveParameter + t)) g := by
  have hw (f : PrincipalSeries (positiveParameter + t)) :
      (rightWord (positiveParameter + t) w f : ComplexGL2 → ℂ) =
        w.foldr (fun X h => rightLieFunction X h) (f : ComplexGL2 → ℂ) := by
    induction w with
    | nil => rfl
    | cons X w ih =>
        change rightLieFunction X ↑(rightWord (positiveParameter + t) w f) = _
        rw [ih]; rfl
  unfold complexSphericalWord
  rw [show complexSpherical (t : ℂ) =
    (sphericalSection (positiveParameter + t) : ComplexGL2 → ℂ) from funext (spherical_real t)]
  exact congrFun (hw _).symm g

private theorem word_factor (w : RealLieWord) (s : ℂ) (g : ComplexGL2)
    (a d : ℂˣ) (b : ℂ) (k : ComplexSU2)
    (hg : g = upperTriangular a d b * complexSU2Embedding k) :
    complexSphericalWord w s g = complexSpherical s g *
      complexSphericalWord w s (complexSU2Embedding k) := by
  have hr : ∀ t : ℝ, complexSphericalWord w t g = complexSpherical t g *
      complexSphericalWord w t (complexSU2Embedding k) := by
    intro t
    rw [word_real, word_real, hg,
      (rightWord (positiveParameter + t) w (sphericalSection (positiveParameter + t))).property.1]
    rw [spherical_real, (sphericalSection (positiveParameter + t)).property.1]
    have hs := RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.spherical_compact
      (positiveParameter + t) k
    rw [hs, mul_one]
  have hs : AnalyticOnNhd ℂ (fun z => complexSpherical z g) Set.univ :=
    complexSphericalWord_holomorphic [] g
  exact congrFun (entire_eq_of_real (complexSphericalWord_holomorphic w g)
    (hs.mul (complexSphericalWord_holomorphic w (complexSU2Embedding k))) hr) s

private theorem band_polynomial (N : ℕ) (f : PrincipalSeries positiveParameter)
    (hf : f ∈ (Finset.range (N + 1)).sup (harmonicKType positiveParameter)) :
    ∃ p : HarmonicVendor.Polynomial,
      p ∈ (Finset.range (N + 1)).sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials ∧
      compactRestriction positiveParameter f = polynomialCompactRestriction p := by
  let I := Finset.range (N + 1)
  have ha : ∀ f ∈ I.sup (harmonicKType positiveParameter), ∃ p : HarmonicVendor.Polynomial,
      p ∈ I.sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials ∧
      compactRestriction positiveParameter f = polynomialCompactRestriction p := by
    apply Finset.sup_induction (p := fun S : Submodule ℂ (PrincipalSeries positiveParameter) =>
      ∀ f ∈ S, ∃ p : HarmonicVendor.Polynomial,
        p ∈ I.sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials ∧
        compactRestriction positiveParameter f = polynomialCompactRestriction p)
    · intro f hf
      have he : f = 0 := by simpa using hf
      subst f
      exact ⟨0, Submodule.zero_mem _, by simp⟩
    · intro S hS T hT f hf
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨p, hp, he⟩ := hS x hx
      obtain ⟨q, hq, hqe⟩ := hT y hy
      exact ⟨p + q, Submodule.add_mem _ hp hq, by rw [map_add, he, hqe, map_add]⟩
    · intro m hm f hf
      obtain ⟨p, hp, he⟩ := KPCplxHarmonicIntertwinerSpectrum.harmonicKType_mem_iff
        positiveParameter m f |>.mp hf
      refine ⟨p, (show KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials m ≤
        I.sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials from Finset.le_sup hm) hp, ?_⟩
      exact funext he
  exact ha f hf

private theorem interpolation_mem_band (μ : Measure ComplexSU2) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (N ℓ : ℕ) (p : HarmonicVendor.Polynomial)
    (hp : p ∈ (Finset.range (N + 1)).sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials)
    (k : ComplexSU2) :
    (2 * ℓ + 1 : ℂ) * (∫ t, star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ t) *
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction p (k * t) ∂μ) =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
        ((Polynomial.aeval CompactInterpolation.pauliCasimir (CompactInterpolation.projectorPolynomial N ℓ)) p) k := by
  have hi (q : HarmonicVendor.Polynomial) : Integrable (fun t =>
      star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ t) *
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction q (k * t)) μ := by
    exact KPCplxHarmonicExtraction.CompactPolynomial.polynomial_character_integrand_integrable
      μ inferInstance ℓ q k |>.congr (Filter.Eventually.of_forall (fun t => rfl))
  have hall : ∀ p ∈ (Finset.range (N + 1)).sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials,
      (2 * ℓ + 1 : ℂ) * (∫ t, star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ t) *
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction p (k * t) ∂μ) =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
        ((Polynomial.aeval CompactInterpolation.pauliCasimir (CompactInterpolation.projectorPolynomial N ℓ)) p) k := by
    apply Finset.sup_induction (p := fun S : Submodule ℂ HarmonicVendor.Polynomial => ∀ p ∈ S,
      (2 * ℓ + 1 : ℂ) * (∫ t, star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ t) *
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction p (k * t) ∂μ) =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
        ((Polynomial.aeval CompactInterpolation.pauliCasimir (CompactInterpolation.projectorPolynomial N ℓ)) p) k)
    · intro p hp
      have he : p = 0 := by simpa using hp
      subst p
      simp
    · intro S hS T hT p hp
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hp
      simp only [map_add, Pi.add_apply, mul_add]
      rw [integral_add (hi x) (hi y), mul_add, hS x hx, hT y hy]
    · intro m hm p hp
      exact CompactInterpolation.character_eq_interpolation_harmonic μ N ℓ m
        (by simpa only [Finset.mem_range] using Nat.le_of_lt_succ (Finset.mem_range.mp hm)) p hp k
  exact hall p hp

private theorem compact_derivative_polynomial (r : ℝ) (j : Fin 3)
    (f : PrincipalSeries r) (p : HarmonicVendor.Polynomial)
    (he : KPCplxHarmonicIntertwinerSpectrum.compactRestriction r f =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction p) :
    KPCplxHarmonicIntertwinerSpectrum.compactRestriction r
      (rightLieDerivative r (HarmonicVendor.compactMatrix j) f) =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction (HarmonicVendor.A j p) := by
  have ht := RepresentationTheory.KPSmoothCoreCasimirEnergy.CompactDerivativeTransport.compact_derivative_transport_of_curves r
    (by
      intro j k
      obtain ⟨c, hc, hd⟩ := RepresentationTheory.KPSmoothCoreCasimirEnergy.CompactDerivativeTransport.compact_trig_curve_exists j k
      exact ⟨c, hc, hd, RepresentationTheory.KPSmoothCoreCasimirEnergy.CompactDerivativeTransport.hopf_derivative_of_matrix_tangent j k c hc hd⟩)
    j p f he
  have hD : rightLieDerivative r (HarmonicVendor.compactMatrix j) f =
      RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.localDerivative r (true, j) f := by
    apply Subtype.ext
    funext g
    change rightLieFunction (HarmonicVendor.compactMatrix j) f g = _
    unfold rightLieFunction
    symm
    exact RepresentationTheory.KPSmoothCoreCasimirEnergy.CasimirHessian.rightDerivative_fderiv r f g _
  rw [hD]
  exact ht

private theorem compact_word_polynomial (r : ℝ) (u : List (Fin 3))
    (f : PrincipalSeries r) (p : HarmonicVendor.Polynomial)
    (he : KPCplxHarmonicIntertwinerSpectrum.compactRestriction r f =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction p) :
    KPCplxHarmonicIntertwinerSpectrum.compactRestriction r
      (rightWord r (u.map HarmonicVendor.compactMatrix) f) =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
        ((CompactInterpolation.compactWord CompactInterpolation.compactGeneratorEnd u) p) := by
  induction u with
  | nil => exact he
  | cons j u ih =>
      exact compact_derivative_polynomial r j _ _ ih

private theorem compact_prefix_profile
    (w : RealLieWord) (u : List (Fin 3)) (n : ℕ)
    (p : Fin n → HarmonicVendor.Polynomial) (a : Fin n → Polynomial ℂ)
    (he : ∀ (s : ℂ) (k : ComplexSU2), complexSphericalWord w s (complexSU2Embedding k) =
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
        (∑ j, (a j).eval s • p j) k) :
    ∀ (s : ℂ) (k : ComplexSU2),
      complexSphericalWord (u.map HarmonicVendor.compactMatrix ++ w) s (complexSU2Embedding k) =
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
          ((CompactInterpolation.compactWord CompactInterpolation.compactGeneratorEnd u)
            (∑ j, (a j).eval s • p j)) k := by
  intro s k
  have hr : ∀ t : ℝ,
      complexSphericalWord (u.map HarmonicVendor.compactMatrix ++ w) t (complexSU2Embedding k) =
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
          ((CompactInterpolation.compactWord CompactInterpolation.compactGeneratorEnd u)
            (∑ j, (a j).eval (t : ℂ) • p j)) k := by
    intro t
    let f := rightWord (positiveParameter + t) w (sphericalSection (positiveParameter + t))
    have hpf : KPCplxHarmonicIntertwinerSpectrum.compactRestriction (positiveParameter + t) f =
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction (∑ j, (a j).eval (t : ℂ) • p j) := by
      funext l
      exact (word_real w t (complexSU2Embedding l)).symm.trans (he t l)
    have ht := compact_word_polynomial (positiveParameter + t) u f _ hpf
    have hw : rightWord (positiveParameter + t) (u.map HarmonicVendor.compactMatrix ++ w)
        (sphericalSection (positiveParameter + t)) =
        rightWord (positiveParameter + t) (u.map HarmonicVendor.compactMatrix) f := by
      exact List.foldr_append
    rw [word_real, hw]
    exact congrFun ht k
  have hR : AnalyticOnNhd ℂ (fun z =>
      KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
        ((CompactInterpolation.compactWord CompactInterpolation.compactGeneratorEnd u)
          (∑ j, (a j).eval z • p j)) k) Set.univ := by
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.analyticOnNhd_fun_sum
    intro j hj
    exact (AnalyticOnNhd.eval_polynomial (a j)).mul analyticOnNhd_const
  exact congrFun (entire_eq_of_real (complexSphericalWord_holomorphic _ _) hR hr) s

private theorem band_profile (w : RealLieWord) :
    ∃ (N n : ℕ) (p : Fin n → HarmonicVendor.Polynomial) (a : Fin n → Polynomial ℂ),
      (∀ j, p j ∈ (Finset.range (N + 1)).sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials) ∧
      ∀ (s : ℂ) (k : ComplexSU2), complexSphericalWord w s (complexSU2Embedding k) =
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction (∑ j, (a j).eval s • p j) k := by
  classical
  obtain ⟨N, n, h, a, hh, he⟩ := sphericalWord_polynomial_harmonic_band w
  have hp := fun j => band_polynomial N (h j) (hh j)
  choose p hband hrestrict using hp
  refine ⟨N, n, p, a, hband, fun s k => ?_⟩
  rw [he]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg ((a j).eval s * ·) (congrFun (hrestrict j) k)

end CompactOrbitProof

theorem sphericalWord_character_projector_words
    (μ : Measure KPCplxCharacterHaar.ComplexSU2) [μ.IsHaarMeasure]
    (hμ : μ Set.univ = 1) :
    ∀ (ℓ : ℕ) (w : KPContHolomorphicKGeneration.RealLieWord),
      ∃ (n : ℕ) (v : Fin n → KPContHolomorphicKGeneration.RealLieWord)
        (c : Fin n → ℂ),
        ∀ (s : ℂ) (g : KPCplxCharacterHaar.ComplexGL2),
          (2 * ℓ + 1 : ℂ) *
            (∫ k : KPCplxCharacterHaar.ComplexSU2,
              star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ k) *
                KPContHolomorphicKGeneration.complexSphericalWord w s
                  (g * KPCplxCharacterHaar.complexSU2Embedding k) ∂μ) =
            ∑ j, c j * KPContHolomorphicKGeneration.complexSphericalWord (v j) s g := by
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_iff.mpr hμ
  letI : IsFiniteMeasure μ := inferInstance
  classical
  intro ℓ w
  obtain ⟨N, m, p, a, hp, he⟩ := CompactOrbitProof.band_profile w
  obtain ⟨n, u, c, hu⟩ := CompactInterpolation.universal_polynomial_compact_words
    (CompactInterpolation.projectorPolynomial N ℓ)
  refine ⟨n, fun j => (u j).map HarmonicVendor.compactMatrix ++ w, c, fun s g => ?_⟩
  obtain ⟨A, D, B, hg⟩ :=
    RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2_factor g
  let k₀ := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2 g
  let q := ∑ j, (a j).eval s • p j
  have hq : q ∈ (Finset.range (N + 1)).sup KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials :=
    Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _ (hp j))
  have hright (k : KPCplxCharacterHaar.ComplexSU2) :
      KPContHolomorphicKGeneration.complexSphericalWord w s
        (g * KPCplxCharacterHaar.complexSU2Embedding k) =
      KPContHolomorphicKGeneration.complexSpherical s g *
        KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction q (k₀ * k) := by
    have hfactor : g * KPCplxCharacterHaar.complexSU2Embedding k =
        KPCplxPrincipalSeriesCharts.upperTriangular A D B *
          KPCplxCharacterHaar.complexSU2Embedding (k₀ * k) := by
      rw [map_mul, ← mul_assoc, ← hg]
    rw [CompactOrbitProof.word_factor w s _ A D B (k₀ * k) hfactor, he]
    have hS : KPContHolomorphicKGeneration.complexSpherical s
        (g * KPCplxCharacterHaar.complexSU2Embedding k) =
        KPContHolomorphicKGeneration.complexSpherical s g := by
      unfold KPContHolomorphicKGeneration.complexSpherical
      change Complex.exp (_ * (Real.log (sphericalRatio (g * KPCplxCharacterHaar.complexSU2Embedding k)) : ℂ)) = _
      rw [sphericalRatio_right_su2]
      rfl
    rw [hS]
  simp_rw [hright]
  have hi : (∫ k : KPCplxCharacterHaar.ComplexSU2,
      star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ k) *
        (KPContHolomorphicKGeneration.complexSpherical s g *
          KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction q (k₀ * k)) ∂μ) =
      KPContHolomorphicKGeneration.complexSpherical s g *
        (∫ k : KPCplxCharacterHaar.ComplexSU2,
          star (KPCplxHarmonicExtraction.su2HarmonicCharacter ℓ k) *
            KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction q (k₀ * k) ∂μ) := by
    simp_rw [mul_left_comm (star _) (KPContHolomorphicKGeneration.complexSpherical s g)]
    exact integral_const_mul _ _
  rw [hi, mul_left_comm (2 * ℓ + 1 : ℂ),
    CompactOrbitProof.interpolation_mem_band μ N ℓ q hq k₀]
  have hh := hu CompactInterpolation.compactGeneratorEnd
  change (Polynomial.aeval CompactInterpolation.pauliCasimir
    (CompactInterpolation.projectorPolynomial N ℓ)) = _ at hh
  rw [hh]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [CompactOrbitProof.word_factor _ s g A D B k₀ hg,
    CompactOrbitProof.compact_prefix_profile w (u j) m p a he]
  dsimp only [q]
  ring

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

end
