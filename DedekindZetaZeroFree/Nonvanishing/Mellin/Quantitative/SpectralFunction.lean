module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Spectral

noncomputable section

open DedekindZetaZeroFree NumberField Filter Topology
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def H (s : ℂ) : ℂ :=
  D.recipe.H s

theorem H_eq_principalContourCorrection (s : ℂ) (hs : 1 < s.re) :
    H D s = PrincipalMellinComparison.principalContourCorrection D.recipe s 1 (1 / 6) := by
  unfold H
  exact (PrincipalMellinComparison.principalContourCorrection_at_double_residue D.recipe s
    (by linarith)).symm

def G (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H D s / D.zetaSCont s

def f (Z : ℝ) : ℂ :=
  if 0 < Z then
    comparisonVerticalIntegral 2 (fun s => (Z : ℂ) ^ (s - 61 / 100) * G D s)
  else 0

def RS : ℂ :=
  comparisonPrincipalResidue F D.recipe.A D.recipe.target D.recipe.probe.principal
    D.recipe.continuation

theorem RS_spec :
    Tendsto (fun s : ℂ => (s - 1) * D.zetaSCont s) (𝓝[≠] 1) (𝓝 (RS D)) := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hR : ContinuousAt D.recipe.continuation.R 1 :=
    (D.recipe.continuation.R_holo.differentiableAt (hopen.mem_nhds (by simp))).continuousAt
  have hE : ContinuousAt (fun s : ℂ => ∏ v ∈ D.recipe.A.Sf,
      (1 - D.recipe.target v.asIdeal * comparisonRealPower (idealNorm v.asIdeal) (-s))) 1 := by
    apply Continuous.continuousAt
    apply continuous_finset_prod
    intro v _
    apply Continuous.sub continuous_const
    apply Continuous.mul continuous_const
    unfold comparisonRealPower
    fun_prop
  have hlim := (hR.mul hE).tendsto
  have hpos : ∀ᶠ s in 𝓝[≠] (1:ℂ), 0 < s.re :=
    eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds (by simp))
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hpos, eventually_mem_nhdsWithin] with s hs hs1
  have hreg := D.recipe.continuation.regularized s hs hs1
  unfold FixedData.zetaSCont
  unfold PrincipalMellin.ActualRecipe.L comparisonPrincipalIncompleteL
  rw [Pi.mul_apply, hreg]
  ring

def c₀ : ℂ := RS D ^ 2 * D.M (1 / 6) * D.W1Hat 1 / 6

end

end DedekindZetaZeroFree.Quantitative.Spectral
