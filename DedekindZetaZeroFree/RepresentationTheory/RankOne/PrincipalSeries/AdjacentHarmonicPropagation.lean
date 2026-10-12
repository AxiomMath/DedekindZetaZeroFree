module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.PrincipalSeries.HarmonicTypeExtraction
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarishChandra.DerivativeOperators

@[expose] public section

open _root_.DedekindZetaZeroFree.KPCplxLoweringCoordinateBoost.Geometry renaming raw_derivative → raw_derivative
open _root_.DedekindZetaZeroFree.KPCplxLoweringCoordinateBoost.Geometry renaming cartanMatrix → cartanMatrix
open _root_.DedekindZetaZeroFree.KPCplxLoweringCoordinateBoost.Geometry renaming rawNoncompactPath → rawNoncompactPath
open _root_.DedekindZetaZeroFree.KPCplxLoweringCoordinateBoost.Geometry renaming noncompactCoefficient → noncompactCoefficient
open _root_.DedekindZetaZeroFree.KPCplxLoweringCoordinateBoost.Geometry renaming noncompactAxis → noncompactAxis

open _root_.DedekindZetaZeroFree.KPCplxHarmonicPropagation renaming compact_polynomial_ne_zero_lowering → compact_polynomial_ne_zero_lowering

noncomputable section
open scoped Classical Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCPropagation
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open NativeComplexHCOperators KPCplxHarmonicPropagation

theorem conformal_gradient_derivative (s : ℝ) (j : Fin 3) (m : ℕ)
    (p : MvPolynomial (Fin 3) ℂ) (f : PrincipalSeries s)
    (hp : p.IsHomogeneous m) (hf : compactRestriction s f = polynomialCompactRestriction p) :
    compactRestriction s (derivative s (KPSmoothCoreCasimirEnergy.cartanMatrix (false,j)) f) =
      noncompactCoefficient j • polynomialCompactRestriction
        (MvPolynomial.pderiv (noncompactAxis j) p - ((m : ℂ) + 1 + 2*(s : ℂ)) •
          (MvPolynomial.X (noncompactAxis j) * p)) := by
  ext k
  exact (hasDerivAt_flow s (KPSmoothCoreCasimirEnergy.cartanMatrix (false,j)) f
    (complexSU2Embedding k)).unique (raw_derivative j s m p f hp hf k)

theorem adjacent_lowering (s : ℝ) (n : ℕ)
    (hcoeff : (((n+1 : ℕ) : ℂ) - 2*(s : ℂ)) / (2*((n+1 : ℕ) : ℂ)+1) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (hLie : ∀ (X : Matrix (Fin 2) (Fin 2) ℂ), Matrix.trace X = 0 →
      ∀ f ∈ U, derivative s X f ∈ U)
    (hn : harmonicKType s (n+1) ≤ U) : harmonicKType s n ≤ U := by
  obtain ⟨v, hvU, hvtype, hv0⟩ := nonzero_adjacent_lowering_of_component s n hcoeff U hn (by
    intro f p hf hp he i
    let j : Fin 3 := ![1,2,0] i
    have hji : noncompactAxis j = i := by fin_cases i <;> rfl
    let c : ℂ := noncompactCoefficient j
    have hc : c ≠ 0 := by
      have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
      fin_cases i <;> simp [c,j,noncompactCoefficient, hsqrt]
    let D := c⁻¹ • derivative s (KPSmoothCoreCasimirEnergy.cartanMatrix (false,j)) f
    have hDU : D ∈ U := U.smul_mem _ (hLie _ (by
      exact (KPSmoothCoreCasimirEnergy.cartan_basis_normalization.1 j).2) f hf)
    have hprofile : compactRestriction s D = polynomialCompactRestriction
        (MvPolynomial.pderiv i p - (((n+1 : ℕ) : ℂ)+1+2*(s : ℂ)) • (MvPolynomial.X i * p)) := by
      rw [map_smul, conformal_gradient_derivative s j (n+1) p f hp.1 he,
        smul_smul, inv_mul_cancel₀ hc, one_smul, hji]
    obtain ⟨a,b,ha,hb,hD,hbprofile⟩ :=
      KPCplxLoweringHarmonicDecomposition.conformal_gradient_harmonic_decomposition s n p hp i D hprofile
    exact ⟨b, lowering_two_harmonic_components_mem s (n+2) n (by omega) U hU a b ha hb
      (by rwa [← hD]), hbprofile⟩)
  exact harmonic_le_of_nonzero_vector s U hU n v hvU hvtype hv0

theorem adjacent_raising (s : ℝ) (n : ℕ) (hcoeff : (n : ℂ)+1+2*(s : ℂ) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (hLie : ∀ (X : Matrix (Fin 2) (Fin 2) ℂ), Matrix.trace X = 0 →
      ∀ f ∈ U, derivative s X f ∈ U)
    (hn : harmonicKType s n ≤ U) : harmonicKType s (n+1) ≤ U := by
  let u := KPCplxHarmonicPropagation.RaisingCalculation.harmonicSection s n
  let p := KPCplxHarmonicPropagation.RaisingCalculation.transverse ^ n
  let D := derivative s (KPSmoothCoreCasimirEnergy.cartanMatrix (false,0)) u
  let c : ℂ := -(Real.sqrt 2 : ℂ) * ((n : ℂ)+1+2*(s : ℂ))
  have hp : p ∈ harmonicPolynomials n :=
    KPCplxHarmonicPropagation.RaisingCalculation.transverse_harmonic n
  have hu : u ∈ harmonicKType s n :=
    KPCplxHarmonicPropagation.RaisingCalculation.harmonicSection_harmonic s n
  have hDU : D ∈ U := hLie _
    (KPSmoothCoreCasimirEnergy.cartan_basis_normalization.1 0).2 u (hn hu)
  have hprof : compactRestriction s D = c • polynomialCompactRestriction (MvPolynomial.X 2 * p) := by
    rw [conformal_gradient_derivative s 0 n p u hp.1
      (KPCplxHarmonicPropagation.RaisingCalculation.harmonicSection_compact s n)]
    have hpartial : MvPolynomial.pderiv 2 p = 0 := by
      simp [p, KPCplxHarmonicPropagation.RaisingCalculation.transverse,
        MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C_mul, Pi.single_apply]
    simp only [noncompactAxis, Matrix.cons_val_zero, hpartial, zero_sub,
      map_neg, map_smul, smul_neg, smul_smul]
    simp only [noncompactCoefficient, Matrix.cons_val_zero, c, neg_mul, neg_smul]
  have hDt : D ∈ harmonicKType s (n+1) := by
    change compactRestriction s D ∈ (harmonicPolynomials (n+1)).map polynomialCompactRestriction
    rw [hprof]
    apply Submodule.smul_mem
    exact ⟨MvPolynomial.X 2 * p,
      KPCplxHarmonicPropagation.RaisingCalculation.height_transverse_harmonic n, rfl⟩
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))) hcoeff
  have hD0 : D ≠ 0 := by
    intro hD
    rw [hD, map_zero] at hprof
    have hpoly : polynomialCompactRestriction (MvPolynomial.X 2 * p) ≠ 0 := by
      have hhom : (MvPolynomial.X 2 * p).IsHomogeneous (n+1) :=
        (KPCplxHarmonicPropagation.RaisingCalculation.height_transverse_harmonic n).1
      have hp0 : MvPolynomial.X 2 * p ≠ 0 := by
        intro hz
        have hval := congrArg (MvPolynomial.eval (![1,0,1] : Fin 3 → ℂ)) hz
        simpa [p, KPCplxHarmonicPropagation.RaisingCalculation.transverse] using hval
      exact compact_polynomial_ne_zero_lowering (n+1) _ hhom hp0
    exact hpoly ((smul_eq_zero.mp hprof.symm).resolve_left hc)
  exact harmonic_le_of_nonzero_vector s U hU (n+1) D hDU hDt hD0

theorem all_harmonics_of_nonzero (s : ℝ)
    (hup : ∀ n : ℕ, (n : ℂ)+1+2*(s : ℂ) ≠ 0)
    (hdown : ∀ n : ℕ, (((n+1 : ℕ) : ℂ)-2*(s : ℂ)) /
      (2*((n+1 : ℕ) : ℂ)+1) ≠ 0)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (hLie : ∀ (X : Matrix (Fin 2) (Fin 2) ℂ), Matrix.trace X = 0 →
      ∀ f ∈ U, derivative s X f ∈ U)
    (f : PrincipalSeries s) (hfU : f ∈ U)
    (hf : f ∈ ⨆ n : ℕ, harmonicKType s n) (hf0 : f ≠ 0) :
    (⨆ n : ℕ, harmonicKType s n) ≤ U := by
  obtain ⟨m, hm⟩ := NativeComplexHCExtraction.harmonic_type_of_nonzero s U hU f hfU hf hf0
  have hzero : harmonicKType s 0 ≤ U := by
    have hdesc : ∀ k, harmonicKType s k ≤ U → harmonicKType s 0 ≤ U := by
      intro k
      induction k with
      | zero => exact id
      | succ k ih =>
        intro hk
        exact ih (adjacent_lowering s k (hdown k) U hU hLie hk)
    exact hdesc m hm
  apply iSup_le
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih => exact adjacent_raising s n (hup n) U hU hLie ih

theorem negative_coefficients_nonzero :
    (∀ n : ℕ, (n : ℂ)+1+2*(negativeParameter : ℂ) ≠ 0) ∧
    (∀ n : ℕ, (((n+1 : ℕ) : ℂ)-2*(negativeParameter : ℂ)) /
      (2*((n+1 : ℕ) : ℂ)+1) ≠ 0) := by
  constructor
  · intro n h
    have hn := Nat.cast_nonneg (α := ℝ) n
    have he := congrArg Complex.re h
    norm_num [negativeParameter] at he
    linarith
  · intro n
    apply div_ne_zero
    · intro h
      have hn := Nat.cast_nonneg (α := ℝ) n
      have he := congrArg Complex.re h
      norm_num [negativeParameter] at he
      linarith
    · intro h
      have hn := Nat.cast_nonneg (α := ℝ) n
      have he := congrArg Complex.re h
      norm_num at he
      linarith

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCPropagation

end
