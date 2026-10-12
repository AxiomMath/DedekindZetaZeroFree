module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.RightDerivedAction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.HarmonicVendor
open KPCplxCharacterHaar KPCplxHarmonicIntertwinerSpectrum MvPolynomial
open scoped BigOperators

abbrev compactMatrix := RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction.compactMatrix

def L (i : Fin 3) (p : Polynomial) : Polynomial :=
  X (i + 1) * pderiv (i + 2) p - X (i + 2) * pderiv (i + 1) p
 def E (p : Polynomial) : Polynomial := ∑ i : Fin 3, X i * pderiv i p

def polynomialCasimir (p : Polynomial) : Polynomial := -(∑ i : Fin 3, L i (L i p))

private theorem polynomialCasimir_eq (p : Polynomial) :
    polynomialCasimir p = E (E p) + E p -
      (∑ i : Fin 3, X i ^ 2) * polynomialLaplacian p := by
  simp only [polynomialCasimir, L, E, polynomialLaplacian, Fin.sum_univ_three,
    LinearMap.add_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
    map_add, map_sub, pderiv_mul, Fin.reduceAdd, pderiv_X, Pi.single_apply]
  norm_num
  ring

theorem polynomialCasimir_harmonic (ℓ : ℕ) (p : Polynomial)
    (hp : p ∈ harmonicPolynomials ℓ) :
    polynomialCasimir p = ((ℓ : ℂ) * ((ℓ : ℂ) + 1)) • p := by
  have he : E p = ℓ • p :=
    (MvPolynomial.mem_homogeneousSubmodule ℓ p).mp hp.1 |>.sum_X_mul_pderiv
  have hee : E (E p) = ℓ • (ℓ • p) := by
    calc
      E (E p) = E (ℓ • p) := by rw [he]
      _ = ℓ • E p := by
        simp only [E, Fin.sum_univ_three, map_nsmul]
        simp only [nsmul_eq_mul]
        ring
      _ = ℓ • (ℓ • p) := by rw [he]
  have hl : polynomialLaplacian p = 0 := hp.2
  rw [polynomialCasimir_eq, hee, he, hl, mul_zero, sub_zero]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_mul, map_add, map_natCast, map_one]
  ring

private theorem L_smul (i : Fin 3) (c : ℂ) (p : Polynomial) :
    L i (c • p) = c • L i p := by
  simp only [L, smul_eq_C_mul, pderiv_C_mul]
  ring

def compactAxis (j : Fin 3) : Fin 3 := ![2, 0, 1] j
def compactCoefficient (j : Fin 3) : ℂ :=
  ![(Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), -(Real.sqrt 2 : ℂ)] j

def A (j : Fin 3) (p : Polynomial) : Polynomial :=
  compactCoefficient j • L (compactAxis j) p

theorem A_casimir (p : Polynomial) :
    -(∑ j : Fin 3, A j (A j p)) = (2 : ℂ) • polynomialCasimir p := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    norm_num
  have hc (j : Fin 3) : compactCoefficient j * compactCoefficient j = 2 := by
    fin_cases j <;> norm_num [compactCoefficient, ← pow_two, hs]
  simp only [A, L_smul, smul_smul, hc]
  simp [compactAxis, polynomialCasimir, Fin.sum_univ_three, smul_add, smul_neg,
    add_comm, add_left_comm, add_assoc]

theorem A_casimir_harmonic (ℓ : ℕ) (p : Harmonic ℓ) :
    -(∑ j : Fin 3, A j (A j p)) = (2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) • (p : Polynomial) := by
  rw [A_casimir, polynomialCasimir_harmonic ℓ p p.property, smul_smul]
  congr 1
  ring

end DedekindZetaZeroFree.HarmonicVendor

end
