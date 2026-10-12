module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents
public import DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormBlocks
public import DedekindZetaZeroFree.Analysis.DyadicLengthBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorCutoffCancellation
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CoreNormalizationData

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound
variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

def idealSize (F : Type) [Field F] [NumberField F] : Ideal (𝓞 F) →* (ℝ≥0) where
  toFun a := (Ideal.absNorm a : ℝ≥0)
  map_one' := by simp
  map_mul' a b := by simp

def pairCharacter (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (u v : Ideal (𝓞 F)) : Ideal (𝓞 F) →* ℂ where
  toFun a := (Q.χ u) a * star ((Q.χ v) a)
  map_one' := by
    simp only [Ideal.one_eq_top, (Q.χ u).map_top', (Q.χ v).map_top', star_one, mul_one]
  map_mul' a b := by
    simp only [(Q.χ u).map_mul', (Q.χ v).map_mul', star_mul]
    ring

def cutoffBase (q d : Ideal (𝓞 F)) (K : ℝ) : Finset (Ideal (𝓞 F)) :=
  idealAdmissibleFinset F (q * d) K

def quotientColumns (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q d : Ideal (𝓞 F)) (N : ℝ) (g : Q.G) : Finset (Ideal (𝓞 F)) :=
  (idealAdmissibleFinset F q (2 * N / (Ideal.absNorm d : ℝ))).filter
    (fun u => u ⊔ d = ⊤ ∧ d * u ∈ paperShell F c N ∧ Q.cls (d * u) = g)

def cutoffDifference (q d : Ideal (𝓞 F)) (K : ℝ)
    (χ : Ideal (𝓞 F) →* ℂ) : ℂ :=
  let H := cutoffBase q d K
  Vendor.CutoffDifference.divisorCutoffSum (idealSize F) χ K H d *
      Vendor.CutoffDifference.moebiusDivisorSum (idealSize F) χ d -
    Vendor.CutoffDifference.baseCutoffSum (idealSize F) χ K H *
      (Vendor.CutoffDifference.density (idealSize F) d : ℂ)

def cancelledMainTerms (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q : Ideal (𝓞 F)) (W : ℝ → ℝ) (kappa : ℂ)
    (M N K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) : ℂ :=
  kappa * (Real.sqrt M : ℂ) *
    ((∫ t in Set.Ioi (0 : ℝ), W (t ^ 2)) : ℂ) *
    ∑ u ∈ quotientColumns Q q d N g, ∑ v ∈ quotientColumns Q q d N g,
      if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
        lam (d * u) * star (lam (d * v)) *
          (Vendor.CutoffDifference.density (idealSize F) (q * u * v) : ℂ) *
          cutoffDifference q d K (pairCharacter Q u v)
      else 0

def shellPrefixEnvelope (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (X Y : ℝ) : ℝ :=
  ((Vendor.dyadicLength (2 * Y) + 1 : ℕ) : ℝ) *
    (1 + X + Y +
      ∑ i ∈ Finset.range (Vendor.dyadicLength X),
        ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * Y)),
          B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i))

def densityRow (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q d : Ideal (𝓞 F)) (N : ℝ) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) (b : Ideal (𝓞 F)) : ℂ :=
  ∑ u ∈ quotientColumns Q q d N g, ∑ v ∈ quotientColumns Q q d N g,
    if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
      lam (d * u) * star (lam (d * v)) *
        (Vendor.CutoffDifference.density (idealSize F) (q * u * v) : ℂ) *
        pairCharacter Q u v b
    else 0

def collectedBoundary (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q d : Ideal (𝓞 F)) (N K : ℝ) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ b ∈ Vendor.CutoffDifference.boundaryElements (cutoffBase q d K) d,
    (Vendor.CutoffDifference.boundaryCoefficient (idealSize F) K
      (cutoffBase q d K) d b : ℂ) /
      (Real.sqrt (Ideal.absNorm b : ℝ) : ℂ) * densityRow Q q d N g lam b

def squarefreeRows (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (q d : Ideal (𝓞 F)) (X N : ℝ) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ t ∈ Vendor.CutoffDifference.divisors d,
    ∑ a ∈ idealAdmissibleFinset F q X,
      ‖densityRow Q q d N g lam (a * t ^ 2)‖

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound

end
