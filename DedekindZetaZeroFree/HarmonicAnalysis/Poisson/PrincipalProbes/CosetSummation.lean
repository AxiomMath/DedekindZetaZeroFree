module

public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerDiscreteness
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalProbes.ResidueSummationAndPrimitivity
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.PrincipalProbes.FourierLatticeSummability

@[expose] public section

namespace DedekindZetaZeroFree.ProbeCoset
noncomputable section
open scoped Classical NumberField

variable {F : Type} [Field F] [NumberField F]

theorem raw_originalTerm_support_finite
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (W : SLocalProduct F A.Sf → ℂ) (hW : HasCompactSupport W)
    (s a : A.R) (hs : s ≠ 0) (X : ℝ) (t : A.G1) :
    (Function.support (originalTerm A D W s a hs X t)).Finite := by
  let d : A.G := (t : A.G) * NormalizedProbe.radialSection A (modulus A s * X)
  have hmul : NormalizedProbe.asLocalPoint A d⁻¹ * NormalizedProbe.asLocalPoint A d = 1 := by
    apply Prod.ext
    · funext v
      simp only [NormalizedProbe.asLocalPoint, SArithmeticData.localToAdditive,
        Prod.fst_mul, Prod.fst_inv, Pi.inv_apply, Units.val_inv_eq_inv_val,
        NumberField.InfiniteAdeleRing, Pi.mul_apply, Pi.one_apply]
      exact inv_mul_cancel₀ (Units.ne_zero _)
    · funext v
      simp [NormalizedProbe.asLocalPoint, SArithmeticData.localToAdditive]
  let C : Set (SLocalProduct F A.Sf) :=
    (fun x => x * NormalizedProbe.asLocalPoint A d) '' tsupport W
  have hC : IsCompact C := hW.image (continuous_id.mul continuous_const)
  have hfin := sIntegerDiagonal_finite_preimage_of_isCompact F A.Sf C hC
  apply hfin.subset
  intro m hm
  have hnon : W (sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A d⁻¹) ≠ 0 := by
    intro hz
    apply hm
    simp only [Function.mem_support, ne_eq] at hm ⊢
    unfold originalTerm
    change _ * W (sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A d⁻¹) = 0
    rw [hz, mul_zero]
  refine ⟨sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A d⁻¹,
    subset_tsupport W hnon, ?_⟩
  change (sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A d⁻¹) *
    NormalizedProbe.asLocalPoint A d = sLocalDiagonal F A.Sf (m : F)
  rw [mul_assoc, hmul, mul_one]

theorem raw_originalTerm_summable
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (W : SLocalProduct F A.Sf → ℂ) (hW : HasCompactSupport W)
    (s a : A.R) (hs : s ≠ 0) (X : ℝ) (t : A.G1) :
    Summable (fun m : A.R => ‖originalTerm A D W s a hs X t m‖) := by
  apply summable_of_hasFiniteSupport
  change (Function.support (fun m : A.R => ‖originalTerm A D W s a hs X t m‖)).Finite
  simpa only [Function.support, norm_ne_zero_iff] using
    raw_originalTerm_support_finite A D W hW s a hs X t

def rowCoefficient (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s a : A.R) (hs : s ≠ 0) (m : A.R) : ℂ := by
  letI := D.finiteResidue s hs
  exact (Real.sqrt (modulus A s) : ℂ)⁻¹ *
    FiniteTransform.gaussSum A.R.toSubring s (D.character s) D.additiveCharacter (-m) *
    D.character a (FiniteTransform.residueMap A.R.toSubring a m)

theorem rowCoefficient_eq_of_residue_eq
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (he : FiniteTransform.IsTrivialOn A.R.toSubring D.additiveCharacter)
    (s a : A.R) (hs : s ≠ 0) (x y : A.R)
    (hxy : FiniteTransform.residueMap A.R.toSubring (s*a) x =
      FiniteTransform.residueMap A.R.toSubring (s*a) y) :
    rowCoefficient A D s a hs x = rowCoefficient A D s a hs y := by
  letI := D.finiteResidue s hs
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hxy)
  have ha : FiniteTransform.residueMap A.R.toSubring a x =
      FiniteTransform.residueMap A.R.toSubring a y := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ⟨s*r, by rw [hr]; ring⟩
  have hg : FiniteTransform.gaussSum A.R.toSubring s (D.character s) D.additiveCharacter (-x) =
      FiniteTransform.gaussSum A.R.toSubring s (D.character s) D.additiveCharacter (-y) := by
    unfold FiniteTransform.gaussSum FiniteTransform.gaussSumWithLifts
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    let l := (FiniteTransform.canonicalLifts A.R.toSubring s).val d
    have hsF : (s : F) ≠ 0 := by exact_mod_cast hs
    have hrF : (s : F)*(a : F)*(r : F) = (x : F)-(y : F) := by exact_mod_cast hr.symm
    have hp : ((-x : A.R) : F) * (l : F) / (s : F) =
        ((-y : A.R) : F) * (l : F) / (s : F) + ((-a*r*l : A.R) : F) := by
      push_cast
      field_simp
      linear_combination (l : F) * hrF
    rw [hp, D.additiveCharacter.map_add_eq_mul, he, mul_one]
  unfold rowCoefficient
  rw [hg, ha]

theorem principal_additiveCharacter_trivial
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS) :
    FiniteTransform.IsTrivialOn A.R.toSubring P.coefficients.additiveCharacter := by
  intro r
  rw [P.sameTrace]
  exact P.traceCompatible r

theorem principal_additiveCharacter_norm
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS) (x : F) :
    ‖P.coefficients.additiveCharacter x‖ = 1 := by
  rw [P.sameTrace]
  unfold ProbeAdditive.phase ProbeAdditive.archPhase
  rw [norm_mul, norm_prod]
  have hexp : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ((∑ v : NumberField.InfinitePlace F, 2 *
      (NumberField.InfinitePlace.Completion.extensionEmbedding v
        ((sLocalDiagonal F A.Sf x).1 v)).re) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp]
  simp

theorem rowCoefficient_finite_transform
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (he : FiniteTransform.IsTrivialOn A.R.toSubring D.additiveCharacter)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (hp : FiniteTransform.IsPrimitiveAt A.R.toSubring s D.additiveCharacter) (h : A.R) :
    (letI := D.finiteResidue s hs
     letI := D.finiteResidue a ha
     letI := D.finiteResidue (s*a) (mul_ne_zero hs ha)
     ∑ r : FiniteTransform.Residue A.R.toSubring (s*a),
       rowCoefficient A D s a hs ((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r) *
       D.additiveCharacter ((h : F) *
         (((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r) : F) /
         ((s : F)*(a : F)))) =
    (letI := D.finiteResidue s hs
     letI := D.finiteResidue a ha
     (Real.sqrt (modulus A s) : ℂ) * FiniteTransform.finiteCoefficient A.R.toSubring s a h
       (D.character s) (D.character a) D.additiveCharacter) := by
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  letI := D.finiteResidue (s*a) (mul_ne_zero hs ha)
  exact FiniteTransform.exact_finite_transform A.R.toSubring s a h hs ha
    (D.character s) (D.character a) D.additiveCharacter he hp

theorem row_sum_eq_sum_residue
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (he : FiniteTransform.IsTrivialOn A.R.toSubring D.additiveCharacter)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (w : A.R → ℂ) (hw : Summable (fun m => rowCoefficient A D s a hs m * w m)) :
    (∑' m : A.R, rowCoefficient A D s a hs m * w m) =
    (letI := D.finiteResidue (s*a) (mul_ne_zero hs ha)
     ∑ r : FiniteTransform.Residue A.R.toSubring (s*a),
       rowCoefficient A D s a hs ((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r) *
       ∑' m : {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r}, w m) := by
  letI := D.finiteResidue (s*a) (mul_ne_zero hs ha)
  have hf := hw.hasSum.tsum_fiberwise (FiniteTransform.residueMap A.R.toSubring (s*a))
  rw [← hf.tsum_eq, tsum_fintype]
  apply Finset.sum_congr rfl
  intro r _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  congr 1
  apply rowCoefficient_eq_of_residue_eq A D he s a hs
  exact m.property.trans ((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).property r).symm

theorem raw_frequencyTerm_summable_of_fourier
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @MeasureTheory.Measure (SLocalProduct F A.Sf) (borel _))
    (W : SLocalProduct F A.Sf → ℂ)
    (he : ∀ x : F, ‖D.additiveCharacter x‖ = 1)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0) (X : ℝ) (t : A.G1)
    (hhat : Summable (fun h : A.R =>
      ‖ProbeWeight.fourier F A.Sf e μ W (frequencyPoint A s a X t h)‖)) :
    Summable (fun h : A.R => ‖frequencyTerm A D e μ W s a hs ha X t h‖) := by
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun h => ?_) (hhat.mul_left (modulus A s * modulus A a))
  unfold frequencyTerm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (FiniteTransform.finiteCoefficient_norm_le A.R.toSubring s a h
      (D.character s) (D.character a) D.additiveCharacter he) (norm_nonneg _)

theorem raw_exact_coset_poisson_of_residue_poisson
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : @MeasureTheory.Measure (SLocalProduct F A.Sf) (borel _))
    (W : SLocalProduct F A.Sf → ℂ) (hW : HasCompactSupport W)
    (he : FiniteTransform.IsTrivialOn A.R.toSubring D.additiveCharacter)
    (hnorm : ∀ x : F, ‖D.additiveCharacter x‖ = 1)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0) (X : ℝ) (t : A.G1)
    (hp : FiniteTransform.IsPrimitiveAt A.R.toSubring s D.additiveCharacter)
    (hhat : Summable (fun h : A.R =>
      ‖ProbeWeight.fourier F A.Sf e μ W (frequencyPoint A s a X t h)‖))
    (hcoset : ∀ r : FiniteTransform.Residue A.R.toSubring (s*a),
      (∑' m : {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r},
        W (sLocalDiagonal F A.Sf (m.val : F) * NormalizedProbe.asLocalPoint A
          (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹))) =
      ((X / modulus A a : ℝ) : ℂ) *
      ∑' h : A.R, D.additiveCharacter ((h : F) *
        (((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r) : F) /
          ((s : F)*(a : F))) *
        ProbeWeight.fourier F A.Sf e μ W (frequencyPoint A s a X t h)) :
    Summable (fun m : A.R => ‖originalTerm A D W s a hs X t m‖) ∧
    Summable (fun h : A.R => ‖frequencyTerm A D e μ W s a hs ha X t h‖) ∧
    (∑' m : A.R, originalTerm A D W s a hs X t m) =
      ((X * Real.sqrt (modulus A s) / modulus A a : ℝ) : ℂ) *
        ∑' h : A.R, frequencyTerm A D e μ W s a hs ha X t h := by
  letI := D.finiteResidue s hs
  letI := D.finiteResidue a ha
  letI := D.finiteResidue (s*a) (mul_ne_zero hs ha)
  refine ⟨raw_originalTerm_summable A D W hW s a hs X t,
    raw_frequencyTerm_summable_of_fourier A D e μ W hnorm s a hs ha X t hhat, ?_⟩
  let w (m : A.R) := W (sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A
    (((t : A.G) * NormalizedProbe.radialSection A (modulus A s * X))⁻¹))
  let H (h : A.R) := ProbeWeight.fourier F A.Sf e μ W (frequencyPoint A s a X t h)
  let c (r : FiniteTransform.Residue A.R.toSubring (s*a)) :=
    rowCoefficient A D s a hs ((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r)
  let phase (r : FiniteTransform.Residue A.R.toSubring (s*a)) (h : A.R) :=
    D.additiveCharacter ((h : F) *
      (((FiniteTransform.canonicalLifts A.R.toSubring (s*a)).val r) : F) / ((s : F)*(a : F)))
  have hsum (r : FiniteTransform.Residue A.R.toSubring (s*a)) :
      Summable (fun h => c r * (phase r h * H h)) := by
    apply Summable.of_norm_bounded (hhat.mul_left ‖c r‖)
    intro h
    simp only [norm_mul, phase, hnorm, one_mul]
    rfl
  have horig : Summable (fun m => rowCoefficient A D s a hs m * w m) := by
    exact (raw_originalTerm_summable A D W hW s a hs X t).of_norm
  change (∑' m : A.R, rowCoefficient A D s a hs m * w m) = _
  rw [row_sum_eq_sum_residue A D he s a hs ha w horig]
  change (∑ r, c r * ∑' m : {m : A.R //
    FiniteTransform.residueMap A.R.toSubring (s*a) m = r}, w m.val) = _
  have hc (r : FiniteTransform.Residue A.R.toSubring (s*a)) :
      (∑' m : {m : A.R // FiniteTransform.residueMap A.R.toSubring (s*a) m = r}, w m.val) =
      ((X / modulus A a : ℝ) : ℂ) * ∑' h : A.R, phase r h * H h := hcoset r
  simp_rw [hc]
  calc
    (∑ r, c r * (((X / modulus A a : ℝ) : ℂ) * ∑' h, phase r h * H h)) =
        ((X / modulus A a : ℝ) : ℂ) * ∑ r, ∑' h, c r * (phase r h * H h) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [tsum_mul_left]
      ring
    _ = ((X / modulus A a : ℝ) : ℂ) *
        ∑' h, (∑ r, c r * phase r h) * H h := by
      rw [← Summable.tsum_finsetSum (fun r _ => hsum r)]
      congr 1
      apply tsum_congr
      intro h
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ((X * Real.sqrt (modulus A s) / modulus A a : ℝ) : ℂ) *
        ∑' h : A.R, frequencyTerm A D e μ W s a hs ha X t h := by
      have ht (h : A.R) : (∑ r, c r * phase r h) =
          (Real.sqrt (modulus A s) : ℂ) *
          FiniteTransform.finiteCoefficient A.R.toSubring s a h
            (D.character s) (D.character a) D.additiveCharacter :=
        rowCoefficient_finite_transform A D he s a hs ha hp h
      simp_rw [ht, mul_assoc]
      rw [tsum_mul_left, ← mul_assoc]
      congr 1
      push_cast
      ring

theorem raw_exact_coset_poisson
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : Normalization A σ η hS P)
    (s a : A.R) (hs : s ≠ 0) (ha : a ≠ 0)
    (X : ℝ) (hX : 0 < X) (t : A.G1) :
    Summable (fun m : A.R =>
      ‖originalTerm A P.coefficients P.W0 s a hs X t m‖) ∧
    Summable (fun h : A.R =>
      ‖frequencyTerm A P.coefficients P.finiteTrace
        P.additiveMeasure P.W0 s a hs ha X t h‖) ∧
    (∑' m : A.R,
      originalTerm A P.coefficients P.W0 s a hs X t m) =
      ((X * Real.sqrt (modulus A s) / modulus A a : ℝ) : ℂ) *
        ∑' h : A.R,
          frequencyTerm A P.coefficients P.finiteTrace
            P.additiveMeasure P.W0 s a hs ha X t h := by
  exact raw_exact_coset_poisson_of_residue_poisson A P.coefficients P.finiteTrace
    P.additiveMeasure P.W0 P.compactSupport
    (principal_additiveCharacter_trivial A σ η hS P)
    (principal_additiveCharacter_norm A σ η hS P) s a hs ha X t
    (raw_principal_additiveCharacter_primitive A σ η hS P N s hs)
    (raw_fourier_norm_summable A σ η hS P N s a hs ha X hX t)
    (raw_residue_poisson A σ η hS P N s a hs ha X hX t)

end
end DedekindZetaZeroFree.ProbeCoset
