module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.OpenCellLaurentProfiles
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ForwardUniformLaurentNumerator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseCompactLaurentAnnulus

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion

open scoped NumberField Valued ValuativeRel Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

variable {X : Type*} [MeasurableSpace X]

def integratedShellNumerator (ν : Measure X) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) : ShellNumerator :=
  ∑ ij ∈ S, Finsupp.single ij (∫ x, c ij x ∂ν)

theorem evaluate_integratedShellNumerator (ν : Measure X) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) (r Q : ℂ) :
    evaluateNumerator (integratedShellNumerator ν S c) r Q =
      ∑ ij ∈ S, (∫ x, c ij x ∂ν) * r ^ ij.1 * Q ^ ij.2 := by
  unfold integratedShellNumerator
  induction S using Finset.induction_on with
  | empty => simp [evaluateNumerator]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [evaluateNumerator, Finsupp.sum_add_index]
    · simp only [Finsupp.sum_single_index, mul_zero, zero_mul, add_zero]
      exact congrArg (_ + ·) ih
    · intro ij; simp
    · intro ij hij b d; ring

theorem integral_finite_shell_expansion (ν : Measure X) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) (hc : ∀ ij ∈ S, Integrable (c ij) ν)
    (r Q den : ℂ) (f : X → ℂ)
    (hf : ∀ x, f x = (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den) :
    Integrable f ν ∧ (∫ x, f x ∂ν) =
      evaluateNumerator (integratedShellNumerator ν S c) r Q / den := by
  have hi : ∀ ij ∈ S, Integrable (fun x => c ij x * r ^ ij.1 * Q ^ ij.2) ν := by
    intro ij hij
    exact ((hc ij hij).mul_const _).mul_const _
  have hs := integrable_finsetSum S hi
  have hfun : f = fun x => (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den := funext hf
  rw [hfun]
  refine ⟨hs.div_const den, ?_⟩
  simp only [div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum S hi, evaluate_integratedShellNumerator]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  rw [integral_mul_const, integral_mul_const]

theorem setIntegral_finite_shell_expansion (ν : Measure X) (E : Set X)
    (hE : MeasurableSet E) (S : Finset (ℤ × ℤ))
    (c : (ℤ × ℤ) → X → ℂ) (hc : ∀ ij ∈ S, IntegrableOn (c ij) E ν)
    (r Q den : ℂ) (f : X → ℂ)
    (hf : ∀ x ∈ E, f x = (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den) :
    IntegrableOn f E ν ∧ (∫ x in E, f x ∂ν) =
      evaluateNumerator (integratedShellNumerator (ν.restrict E) S c) r Q / den := by
  let g : X → ℂ := fun x => (∑ ij ∈ S, c ij x * r ^ ij.1 * Q ^ ij.2) / den
  obtain ⟨hi, he⟩ := integral_finite_shell_expansion (ν.restrict E) S c hc r Q den g
    (fun _ => rfl)
  exact ⟨IntegrableOn.congr_fun hi (fun x hx => (hf x hx).symm) hE,
    (setIntegral_congr_fun hE hf).trans he⟩

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion
