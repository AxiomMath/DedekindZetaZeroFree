module

public import DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteTensorProducts
public import DedekindZetaZeroFree.Theta.Digits.SexticReflectedLocalModel
public import DedekindZetaZeroFree.Moments.Comparison.PoissonMellinKernelData

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical

def thetaReflectionGaussian (x : ℝ) : ℝ :=
  if 0 < x then Real.exp (-(Real.log x) ^ 2 / 4) / (2 * Real.sqrt Real.pi) else 0

theorem thetaReflectionGaussian_of_pos (x : ℝ) (hx : 0 < x) :
    thetaReflectionGaussian x =
      Real.exp (-(Real.log x) ^ 2 / 4) / (2 * Real.sqrt Real.pi) := by
  simp [thetaReflectionGaussian, hx]

namespace ThetaReflectionData

variable {F : Type} [Field F] [NumberField F]

def rationalGamma (A : SArithmeticData F) : Subgroup Fˣ :=
  A.U.map (powMonoidHom 6)

abbrev Frequency (A : SArithmeticData F) := Fˣ ⧸ rationalGamma A

abbrev Row (A : SArithmeticData F) := {m : A.R // m ≠ 0}

def rowUnit (A : SArithmeticData F) (m : Row A) : Fˣ :=
  Units.mk0 (m.val : F) (by
    intro h
    apply m.property
    apply Subtype.ext
    exact h)

def rationalNorm (A : SArithmeticData F) (ν : Fˣ) : ℝ :=
  A.norm (A.diagonal ν)

def rationalClass (A : SArithmeticData F) : Fˣ →* A.V :=
  (QuotientGroup.mk' A.sixthPowers).comp A.diagonal

private theorem norm_mul' (A : SArithmeticData F) (x y : A.G) :
    A.norm (x * y) = A.norm x * A.norm y := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Units.val_mul,
    norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

private theorem norm_pos_diagonal (A : SArithmeticData F) (ν : Fˣ) :
    0 < A.norm (A.diagonal ν) := by
  simp only [SArithmeticData.norm]
  apply mul_pos
  · apply Finset.prod_pos
    intro w _
    apply pow_pos
    exact norm_pos_iff.mpr (Units.ne_zero ((A.diagonal ν).1 w))
  · apply Finset.prod_pos
    intro v _
    exact norm_pos_iff.mpr (Units.ne_zero ((A.diagonal ν).2 v))

theorem rationalGamma_le_class_ker (A : SArithmeticData F) :
    rationalGamma A ≤ (rationalClass A).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  show QuotientGroup.mk' A.sixthPowers (A.diagonal x) = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨A.diagonal u, by simp only [powMonoidHom_apply]; rw [map_pow]⟩

def frequencyClass (A : SArithmeticData F) : Frequency A →* A.V :=
  QuotientGroup.lift (rationalGamma A) (rationalClass A)
    (rationalGamma_le_class_ker A)

@[simp] theorem frequencyClass_mk (A : SArithmeticData F) (ν : Fˣ) :
    frequencyClass A (QuotientGroup.mk ν) = rationalClass A ν := by
  rfl

theorem rationalNorm_eq_of_rel (A : SArithmeticData F) (ν ν' : Fˣ)
    (h : QuotientGroup.leftRel (rationalGamma A) ν ν') :
    rationalNorm A ν = rationalNorm A ν' := by
  rw [QuotientGroup.leftRel_apply] at h
  obtain ⟨u, hu, hu6⟩ := Subgroup.mem_map.mp h
  have hmem : A.diagonal (ν⁻¹ * ν') ∈ A.Gamma := by
    rw [← hu6]
    exact Subgroup.mem_map_of_mem A.diagonal
      (Subgroup.mem_map_of_mem (powMonoidHom 6) hu)
  have h1 : A.norm (A.diagonal (ν⁻¹ * ν')) = 1 := SArithmeticData.Gamma_le_G1 A hmem
  have hd : A.diagonal ν' = A.diagonal ν * A.diagonal (ν⁻¹ * ν') := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [rationalNorm, rationalNorm, hd, norm_mul', h1, mul_one]

def frequencyNorm (A : SArithmeticData F) : Frequency A → ℝ :=
  Quotient.lift (rationalNorm A) (rationalNorm_eq_of_rel A)

@[simp] theorem frequencyNorm_mk (A : SArithmeticData F) (ν : Fˣ) :
    frequencyNorm A (QuotientGroup.mk ν) = A.norm (A.diagonal ν) := rfl

theorem frequencyNorm_pos (A : SArithmeticData F) (ν : Frequency A) :
    0 < frequencyNorm A ν := by
  induction ν using QuotientGroup.induction_on with
  | _ ν' =>
    rw [frequencyNorm_mk]
    exact norm_pos_diagonal A ν'

def forwardModulus (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) : A.R :=
  D.generator c.val * D.generator n ^ 3

def forwardArithmeticWeight (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) : ℂ :=
  D.gammaTwo c * D.theta (forwardModulus A D c n)

def forwardRowCharacter (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) (m : A.R) : ℂ :=
  D.character (forwardModulus A D c n)
    (FiniteTransform.residueMap A.R.toSubring (forwardModulus A D c n) m)

def forwardSummand (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (m : Row A) (Z : ℝ)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) : ℂ :=
  forwardArithmeticWeight A D c n * forwardRowCharacter A D c n m.val *
    (thetaReflectionGaussian (A.exteriorNorm c.val * A.exteriorNorm n ^ 3 / Z) : ℂ) /
    ((Real.sqrt (A.exteriorNorm c.val) : ℂ) * (A.exteriorNorm n : ℂ))

def forwardB (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (m : Row A) (Z : ℝ) : ℂ :=
  ∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior,
    forwardSummand A D m Z i.1 i.2

def gammaTwoRecipe (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) : ℂ := by
  letI := D.finiteResidue (D.generator c.val) (D.generates c.val).1
  exact (Real.sqrt (A.exteriorNorm c.val) : ℂ)⁻¹ *
    FiniteTransform.gaussSum A.R.toSubring (D.generator c.val)
      (D.character (D.generator c.val) ^ 2) D.additiveCharacter 1

def GammaTwoCompatibility (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) : Prop :=
  ∀ c, D.gammaTwo c = gammaTwoRecipe A D c

def SixthUnitCharacterCompatibility (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) : Prop :=
  ∀ (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) (u : A.Rˣ),
    D.character (forwardModulus A D c n)
      (FiniteTransform.residueMap A.R.toSubring (forwardModulus A D c n)
        ((u : A.R) ^ 6)) = 1

def sixthTranslate (A : SArithmeticData F) (u : A.Rˣ) (m : Row A) : Row A :=
  ⟨(u : A.R) ^ 6 * m.val, mul_ne_zero (pow_ne_zero _ u.ne_zero) m.property⟩

theorem forwardSummand_sixthTranslate (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : SixthUnitCharacterCompatibility A D) (u : A.Rˣ) (m : Row A) (Z : ℝ)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    forwardSummand A D (sixthTranslate A u m) Z c n =
      forwardSummand A D m Z c n := by
  have hc : forwardRowCharacter A D c n (sixthTranslate A u m).val =
      forwardRowCharacter A D c n m.val := by
    simp only [forwardRowCharacter, sixthTranslate, map_mul, hD c n u, one_mul]
  simp only [forwardSummand, hc]

theorem forwardB_sixthTranslate (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (hD : SixthUnitCharacterCompatibility A D) (u : A.Rˣ) (m : Row A) (Z : ℝ) :
    forwardB A D (sixthTranslate A u m) Z = forwardB A D m Z := by
  apply tsum_congr
  intro i
  exact forwardSummand_sixthTranslate A D hD u m Z i.1 i.2

end ThetaReflectionData
end
end DedekindZetaZeroFree
