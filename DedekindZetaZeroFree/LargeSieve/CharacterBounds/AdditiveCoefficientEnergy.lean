module

public import DedekindZetaZeroFree.Moments.Probes.QuotientMeasureAndArithmeticInvariance

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeCoefficientEnergy
noncomputable section
open scoped Classical

theorem finite_row_minkowski {ι κ : Type*} (M : Finset ι)
    (f : κ → ι → ℂ) (u : κ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ j, 0 ≤ u j) (hsum : Summable u)
    (hmode : ∀ j, (∑ m ∈ M, ‖f j m‖ ^ 2) ≤ B * (u j) ^ 2) :
    (∀ m ∈ M, Summable (fun j => f j m)) ∧
      (∑ m ∈ M, ‖∑' j, f j m‖ ^ 2) ≤ B * (∑' j, u j) ^ 2 := by
  classical
  let g : κ → EuclideanSpace ℂ ↥M := fun j => WithLp.toLp 2 (fun m : ↥M => f j m.1)

  have hgnorm_sq : ∀ j, ‖g j‖ ^ 2 = ∑ m ∈ M, ‖f j m‖ ^ 2 := by
    intro j
    rw [EuclideanSpace.norm_sq_eq]
    simp only [g, PiLp.toLp_apply]
    rw [← Finset.sum_subtype M (fun x => Iff.rfl) (fun a => ‖f j a‖ ^ 2)]

  have hgnorm : ∀ j, ‖g j‖ ≤ Real.sqrt B * u j := by
    intro j
    have h1 : ‖g j‖ ^ 2 ≤ B * (u j) ^ 2 := by rw [hgnorm_sq j]; exact hmode j
    have h2 : ‖g j‖ ≤ Real.sqrt (B * (u j) ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg (g j))]
      exact Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul hB, Real.sqrt_sq (hu j)] at h2
  have hsumg : Summable g :=
    Summable.of_norm_bounded (hsum.mul_left (Real.sqrt B)) hgnorm
  have hsum_norm : Summable (fun j => ‖g j‖) :=
    Summable.of_norm_bounded (hsum.mul_left (Real.sqrt B))
      (fun j => by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hgnorm j)

  have hnorm_tsum : ‖∑' j, g j‖ ≤ Real.sqrt B * (∑' j, u j) := by
    calc ‖∑' j, g j‖ ≤ ∑' j, ‖g j‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' j, Real.sqrt B * u j :=
          Summable.tsum_le_tsum hgnorm hsum_norm (hsum.mul_left _)
      _ = Real.sqrt B * ∑' j, u j := tsum_mul_left

  have hkey : (∑' j, g j).ofLp = fun m : ↥M => ∑' j, f j m.1 := by
    funext m
    have hsum_e : Summable (fun j => (EuclideanSpace.equiv ↥M ℂ) (g j)) :=
      hsumg.mapL (EuclideanSpace.equiv ↥M ℂ : EuclideanSpace ℂ ↥M →L[ℂ] (↥M → ℂ))
    calc (∑' j, g j).ofLp m
        = ((EuclideanSpace.equiv ↥M ℂ) (∑' j, g j)) m := rfl
      _ = ((∑' j, (EuclideanSpace.equiv ↥M ℂ) (g j))) m := by
            rw [ContinuousLinearEquiv.map_tsum]
      _ = ∑' j, (EuclideanSpace.equiv ↥M ℂ) (g j) m := Pi.tsum_apply hsum_e
      _ = ∑' j, f j m.1 := by
            apply tsum_congr
            intro j
            simp only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, g, PiLp.toLp_apply]

  have hsq : ‖∑' j, g j‖ ^ 2 = ∑ m ∈ M, ‖∑' j, f j m‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, hkey]
    simp only
    rw [← Finset.sum_subtype M (fun x => Iff.rfl) (fun a => ‖∑' j, f j a‖ ^ 2)]
  refine ⟨?_, ?_⟩
  · intro m hm
    simpa only [EuclideanSpace.coe_proj, g, PiLp.toLp_apply] using
      hsumg.mapL (EuclideanSpace.proj (𝕜 := ℂ) ⟨m, hm⟩)
  · rw [← hsq]
    calc ‖∑' j, g j‖ ^ 2 ≤ (Real.sqrt B * (∑' j, u j)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm_tsum 2
      _ = B * (∑' j, u j) ^ 2 := by rw [mul_pow, Real.sq_sqrt hB]

end
end DedekindZetaZeroFree.ProbeCoefficientEnergy

end

section

namespace DedekindZetaZeroFree.ProbeCoefficientEnergy
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]

private theorem sum_units {R : Type*} [CommMonoid R] [Fintype R]
    {M : Type*} [AddCommMonoid M] (f : R → M)
    (hf : ∀ x, ¬IsUnit x → f x = 0) :
    (∑ x : Rˣ, f x) = ∑ x : R, f x := by
  apply Fintype.sum_of_injective (fun x : Rˣ => (x : R)) Units.val_injective
  · intro x hx
    apply hf
    simpa only [Set.mem_range, IsUnit] using hx
  · intro x; rfl
 def presentation (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A) :
    ProbeSeparation.Presentation F A.Sf where
  generator I hI := D.generator (A.exteriorIdealEquiv.symm ⟨I,hI⟩)
  generator_nonzero I hI := (D.generates _).1
  generator_span I hI := by
    have h := (D.generates (A.exteriorIdealEquiv.symm ⟨I,hI⟩)).2
    exact h.trans (congrArg Subtype.val (A.exteriorIdealEquiv.apply_symm_apply ⟨I,hI⟩))
  lift I d := Quotient.out (d : A.R ⧸ I)
  lift_spec I d := Quotient.out_eq _
private theorem generator_eq (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s : A.Exterior) (h : Ideal.span {D.generator s} ≠ ⊥) :
    (presentation A D).generator (Ideal.span {D.generator s}) h = D.generator s := by
  change D.generator (A.exteriorIdealEquiv.symm _) = _
  congr 1
  apply A.exteriorIdealEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (D.generates s).2
 theorem span_ne (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s : A.Exterior) : Ideal.span {D.generator s} ≠ ⊥ := by
  rw [(D.generates s).2]
  exact A.extendIdeal_ne_zero s
 def rho (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (T : Finset A.Exterior) (i : Σ s : ↥T, (FiniteTransform.Residue A.R.toSubring (D.generator s))ˣ) :
    ProbeSeparation.ReducedPair F A.Sf := ⟨⟨Ideal.span {D.generator i.1}, span_ne A D i.1⟩, i.2⟩
private theorem rho_injective (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (T : Finset A.Exterior) : Function.Injective (rho A D T) := by
  apply Function.Injective.sigma_map
    (β₂ := fun I : {I : Ideal A.R // I ≠ ⊥} => (A.R ⧸ I.val)ˣ)
    (f₁ := fun s : ↥T => (⟨Ideal.span {D.generator s}, span_ne A D s⟩ : {I : Ideal A.R // I ≠ ⊥}))
    (f₂ := fun _ d => d)
  · intro s t h
    apply Subtype.ext
    apply A.exteriorIdealEquiv.injective
    apply Subtype.ext
    simpa only [A.exteriorIdealEquiv_apply, ← (D.generates s).2, ← (D.generates t).2] using congrArg Subtype.val h
  · intro s x y h; exact h
private theorem rho_norm (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (T : Finset A.Exterior) (i : Σ s : ↥T, (FiniteTransform.Residue A.R.toSubring (D.generator s))ˣ) :
    ProbeSeparation.denominatorNorm F (rho A D T i) = A.exteriorNorm i.1 := by
  change (Nat.card (A.R ⧸ Ideal.span {D.generator i.1}) : ℝ) = _
  rw [(D.generates i.1).2, A.exteriorResidue_card]
  rfl
private theorem row_mem (A : SArithmeticData F) (N : ℝ) (hN : 1 ≤ N)
    (K : Set A.G) {m : A.R} (hm : m ∈ NormalizedProbe.scaledIntegralRows A N K) :
    m ∈ ProbeAdditive.boxRows F A.Sf N (NormalizedProbe.asLocalPoint A '' K) := by
  obtain ⟨k, hk, he⟩ := hm
  refine ⟨NormalizedProbe.asLocalPoint A k, ⟨k,hk,rfl⟩, ?_⟩
  rw [he]
  have hmul : ∀ x y : A.G, NormalizedProbe.asLocalPoint A (x*y) =
      NormalizedProbe.asLocalPoint A x * NormalizedProbe.asLocalPoint A y := by
    intro x y; ext <;> rfl
  rw [hmul]
  simp only [NormalizedProbe.radialSection, dif_pos (by linarith : 0 < N),
    NormalizedProbe.asLocalPoint, SArithmeticData.localToAdditive_radialSection]
private theorem point_continuous (A : SArithmeticData F) : Continuous (NormalizedProbe.asLocalPoint A) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)
  · apply continuous_pi
    intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
private theorem indexed_sieve (A : SArithmeticData F)
    (e : (v : A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (K : Set A.G) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N V : ℝ, 1 ≤ N → 1 ≤ V →
    ∀ (M : Finset A.R), (↑M : Set A.R) ⊆ NormalizedProbe.scaledIntegralRows A N K →
    ∀ (I : Type) [Fintype I] (p : ProbeSeparation.Presentation F A.Sf)
      (r : I → ProbeSeparation.ReducedPair F A.Sf), Function.Injective r →
      (∀ i, ProbeSeparation.denominatorNorm F (r i) ≤ V) → ∀ b : I → ℂ,
    (∑ m ∈ M, ‖∑ i, b i * ProbeAdditive.phase F A.Sf e
      (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F p (r i))))‖ ^ 2) ≤
    C * (N + V^2) * ∑ i, ‖b i‖^2 := by
  let K' := NormalizedProbe.asLocalPoint A '' K
  have hK' : IsCompact K' := hK.image (point_continuous A)
  obtain ⟨C, hC, hb⟩ := probe_additive_row_box_sieve F A.zeta12 A.primitive_zeta12
    A.Sf e he htrace K' hK'
  refine ⟨C, hC, ?_⟩
  intro N V hN hV M hM I inst p r hr hnorm b
  let P := Finset.univ.image r
  let E : I ≃ ↥P := Equiv.ofBijective
    (fun i => ⟨r i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro i j h; exact hr (congrArg Subtype.val h)
      · intro x; obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
        exact ⟨i, Subtype.ext hi⟩)
  have hP : ∀ x ∈ P, ProbeSeparation.denominatorNorm F x ≤ V := by
    intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hnorm i
  let bP : ↥P → ℂ := fun x => b (E.symm x)
  have hinner (m : A.R) :
      (∑ i, b i * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F p (r i))))) =
      ∑ x : ↥P, bP x * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F p x.val))) := by
    apply Fintype.sum_equiv E
    intro i
    change b i * _ = b (E.symm (E i)) * _
    rw [E.symm_apply_apply]
    rfl
  have henergy : (∑ x : ↥P, ‖bP x‖^2) = ∑ i, ‖b i‖^2 := by
    symm; apply Fintype.sum_equiv E
    intro i; simp [bP]
  let rows := (probe_additive_box_rows_finite F A.Sf N K' hK').toFinset
  have hsub : M ⊆ rows := by
    intro m hm
    simpa only [rows, Set.Finite.mem_toFinset] using (row_mem A N hN K (hM hm))
  have hh := (hb N V hN hV p P hP).1 (fun x => starRingEnd ℂ (bP x))
  have hphase (m : A.R) (x : ↥P) :
      ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F p x.val))) =
      starRingEnd ℂ (ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf ((m : F) * ProbeSeparation.value F p x.val))) := by
    rw [map_neg, ProbeAdditive.phase_neg]
  have hneg (m : A.R) :
      ‖∑ x : ↥P, bP x * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F p x.val)))‖ =
      ‖∑ x : ↥P, starRingEnd ℂ (bP x) * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf ((m : F) * ProbeSeparation.value F p x.val))‖ := by
    rw [← Complex.norm_conj]
    simp only [map_sum, map_mul, hphase, RingHomCompTriple.comp_apply,
      starRingEnd_self_apply, RingHom.id_apply]
  simp only [Complex.norm_conj] at hh
  rw [henergy] at hh
  have hrowsum : (∑ m : ↥rows, ‖∑ x : ↥P, starRingEnd ℂ (bP x) * ProbeAdditive.phase F A.Sf e
      (sLocalDiagonal F A.Sf ((m.val : F) * ProbeSeparation.value F p x.val))‖^2) =
      ∑ m ∈ rows, ‖∑ x : ↥P, starRingEnd ℂ (bP x) * ProbeAdditive.phase F A.Sf e
      (sLocalDiagonal F A.Sf ((m : F) * ProbeSeparation.value F p x.val))‖^2 := Finset.sum_coe_sort rows (fun m : A.R => ‖∑ x : ↥P, starRingEnd ℂ (bP x) * ProbeAdditive.phase F A.Sf e
      (sLocalDiagonal F A.Sf ((m : F) * ProbeSeparation.value F p x.val))‖^2)
  rw [hrowsum] at hh
  calc
    _ = ∑ m ∈ M, ‖∑ x : ↥P, starRingEnd ℂ (bP x) * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf ((m : F) * ProbeSeparation.value F p x.val))‖^2 := by
      apply Finset.sum_congr rfl; intro m hm; rw [hinner, hneg]
    _ ≤ ∑ m ∈ rows, ‖∑ x : ↥P, starRingEnd ℂ (bP x) * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf ((m : F) * ProbeSeparation.value F p x.val))‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ _ := hh
private theorem phase_eq (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (e : (v : A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (hsame : ∀ x : F, D.additiveCharacter x = ProbeAdditive.phase F A.Sf e (sLocalDiagonal F A.Sf x))
    (T : Finset A.Exterior) (i : Σ s : ↥T, (FiniteTransform.Residue A.R.toSubring (D.generator s))ˣ)
    (m : A.R) :
    ProbeAdditive.phase F A.Sf e (sLocalDiagonal F A.Sf (-((m : F) *
      ProbeSeparation.value F (presentation A D) (rho A D T i)))) =
    D.additiveCharacter ((-m : A.R) * (FiniteTransform.canonicalLifts A.R.toSubring (D.generator i.1)).val i.2 / (D.generator i.1 : F)) := by
  rw [hsame]
  congr 1
  change sLocalDiagonal F A.Sf (-( (m : F) * (((Quotient.out (i.2 : FiniteTransform.Residue A.R.toSubring (D.generator i.1)) : A.R) : F) /
    ((presentation A D).generator (Ideal.span {D.generator i.1}) (span_ne A D i.1) : F)))) = _
  rw [generator_eq A D i.1 (span_ne A D i.1)]
  congr 1
  change -( (m : F) * (((Quotient.out (i.2 : FiniteTransform.Residue A.R.toSubring (D.generator i.1)) : A.R) : F) / (D.generator i.1 : F))) = _
  simp only [FiniteTransform.canonicalLifts, Subalgebra.coe_neg]
  ring
 def coeff (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (Y L : ℝ) (j : ℤ) (s : A.Exterior)
    (d : FiniteTransform.Residue A.R.toSubring (D.generator s)) : ℂ :=
  (Y⁻¹ : ℂ) * (Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ * D.character (D.generator s) d *
    ProbeLogWeight.mode L j (A.exteriorNorm s / Y)
private theorem expansion (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (e : (v : A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (hsame : ∀ x : F, D.additiveCharacter x = ProbeAdditive.phase F A.Sf e (sLocalDiagonal F A.Sf x))
    (T : Finset A.Exterior) (Y L : ℝ) (j : ℤ) (m : A.R) :
    (Y⁻¹ : ℂ) * ∑ s ∈ T, NormalizedProbe.gaussRow A D s m *
      ProbeLogWeight.mode L j (A.exteriorNorm s / Y) =
    (letI := fun s : ↥T => D.finiteResidue (D.generator s) (D.generates s).1
    ∑ i : (Σ s : ↥T, (FiniteTransform.Residue A.R.toSubring (D.generator s))ˣ),
      coeff A D Y L j i.1 i.2 * ProbeAdditive.phase F A.Sf e
      (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F (presentation A D) (rho A D T i))))) := by
  letI := fun s : ↥T => D.finiteResidue (D.generator s) (D.generates s).1
  rw [Fintype.sum_sigma, ← Finset.sum_coe_sort T]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [NormalizedProbe.gaussRow, FiniteTransform.gaussSum, FiniteTransform.gaussSumWithLifts]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  have hu := sum_units (fun d : FiniteTransform.Residue A.R.toSubring (D.generator s) =>
      (Y⁻¹ : ℂ) * ((Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ * (D.character (D.generator s) d *
        D.additiveCharacter ((-m : A.R) * (FiniteTransform.canonicalLifts A.R.toSubring (D.generator s)).val d / (D.generator s : F))) *
        ProbeLogWeight.mode L j (A.exteriorNorm s / Y)))
    (by intro d hd; simp [MulChar.map_nonunit _ hd])
  rw [← hu]
  apply Finset.sum_congr rfl
  intro d hd
  rw [phase_eq A D e hsame T ⟨s,d⟩ m]
  dsimp [coeff]
  ring

theorem gauss_mode_row_sieve (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (e : (v : A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (hsame : ∀ x : F, D.additiveCharacter x =
      ProbeAdditive.phase F A.Sf e (sLocalDiagonal F A.Sf x))
    (K : Set A.G) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N V : ℝ), 1 ≤ N → 1 ≤ V →
      ∀ (M : Finset A.R), (↑M : Set A.R) ⊆ NormalizedProbe.scaledIntegralRows A N K →
      ∀ (T : Finset A.Exterior), (∀ s ∈ T, A.exteriorNorm s ≤ V) →
      ∀ (Y L : ℝ) (j : ℤ),
        (∑ m ∈ M, ‖(Y⁻¹ : ℂ) * ∑ s ∈ T,
          NormalizedProbe.gaussRow A D s m *
            ProbeLogWeight.mode L j (A.exteriorNorm s / Y)‖ ^ 2) ≤
        C * (N + V ^ 2) * ∑ s ∈ T,
          (letI := D.finiteResidue (D.generator s) (D.generates s).1
           ∑ d : FiniteTransform.Residue A.R.toSubring (D.generator s),
             ‖(Y⁻¹ : ℂ) * (Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ *
               D.character (D.generator s) d *
                 ProbeLogWeight.mode L j (A.exteriorNorm s / Y)‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := indexed_sieve A e he htrace K hK
  refine ⟨C, hC, ?_⟩
  intro N V hN hV M hM T hT Y L j
  letI := fun s : ↥T => D.finiteResidue (D.generator s) (D.generates s).1
  let I := Σ s : ↥T, (FiniteTransform.Residue A.R.toSubring (D.generator s))ˣ
  have hnorm : ∀ i : I, ProbeSeparation.denominatorNorm F (rho A D T i) ≤ V := by
    intro i
    rw [rho_norm]
    exact hT i.1 i.1.property
  have hh := hb N V hN hV M hM I (presentation A D) (rho A D T)
    (rho_injective A D T) hnorm (fun i => coeff A D Y L j i.1 i.2)
  have heng : (∑ i : I, ‖coeff A D Y L j i.1 i.2‖^2) =
      ∑ s ∈ T, (letI := D.finiteResidue (D.generator s) (D.generates s).1
      ∑ d : FiniteTransform.Residue A.R.toSubring (D.generator s),
        ‖coeff A D Y L j s d‖^2) := by
    rw [Fintype.sum_sigma, ← Finset.sum_coe_sort T]
    apply Finset.sum_congr rfl
    intro s hs
    exact sum_units (fun d : FiniteTransform.Residue A.R.toSubring (D.generator s) => ‖coeff A D Y L j s d‖^2)
      (by intro d hd; simp [coeff, MulChar.map_nonunit _ hd])
  rw [heng] at hh
  have hleft : (∑ m ∈ M, ‖(Y⁻¹ : ℂ) * ∑ s ∈ T,
      NormalizedProbe.gaussRow A D s m * ProbeLogWeight.mode L j (A.exteriorNorm s / Y)‖^2) =
      ∑ m ∈ M, ‖∑ i : I, coeff A D Y L j i.1 i.2 * ProbeAdditive.phase F A.Sf e
        (sLocalDiagonal F A.Sf (-((m : F) * ProbeSeparation.value F (presentation A D) (rho A D T i))))‖^2 := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [expansion A D e hsame T Y L j m]
  rw [hleft]
  exact hh

end
end DedekindZetaZeroFree.ProbeCoefficientEnergy

end

section

namespace DedekindZetaZeroFree.ProbeCoefficientEnergy
noncomputable section
open scoped Classical NumberField BoundedContinuousFunction
variable {F : Type} [Field F] [NumberField F]

theorem separated_finite_row_energy (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (e : (v : A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (htrace : ProbeAdditive.TraceCompatible F A.Sf e)
    (hsame : ∀ x : F, D.additiveCharacter x =
      ProbeAdditive.phase F A.Sf e (sLocalDiagonal F A.Sf x))
    (K : Set A.G) (hK : IsCompact K)
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ) (hc : Summable (fun j => ‖c j‖))
    (v0 v1 E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ Y : ℝ, 1 ≤ Y → ∀ (L : ℝ) (j : ℤ) (T : Finset A.Exterior),
      (∀ s ∈ T, v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y) →
      (∑ s ∈ T,
        (letI := D.finiteResidue (D.generator s) (D.generates s).1
         ∑ d : FiniteTransform.Residue A.R.toSubring (D.generator s),
           ‖(Y⁻¹ : ℂ) * (Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ *
             D.character (D.generator s) d *
               ProbeLogWeight.mode L j (A.exteriorNorm s / Y)‖ ^ 2)) ≤ E / Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y : ℝ), 1 ≤ X → 1 ≤ Y →
      ∀ (M : Finset A.R),
        (↑M : Set A.R) ⊆ NormalizedProbe.scaledIntegralRows A (X * Y) K →
      ∀ (T : Finset A.Exterior),
        (∀ s ∈ T, v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y) →
      ∀ (L : ℝ) (y : A.R → SLocalProduct F A.Sf),
        (∑ m ∈ M, ‖(Real.sqrt (X * Y) : ℂ)⁻¹ *
          ((Y⁻¹ : ℂ) * ∑' j : ℤ, c j (y m) * ∑ s ∈ T,
            NormalizedProbe.gaussRow A D s m *
              ProbeLogWeight.mode L j (A.exteriorNorm s / Y))‖ ^ 2) ≤
        C * (X * Y)⁻¹ * (X * Y + Y ^ 2) / Y := by
  obtain ⟨C₀, hC₀, hsieve⟩ := gauss_mode_row_sieve A D e he htrace hsame K hK
  let a : ℝ := max 1 v1
  have ha : 1 ≤ a := le_max_left _ _
  have ha0 : 0 ≤ a := le_trans zero_le_one ha
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  let S : ℝ := ∑' j : ℤ, ‖c j‖
  refine ⟨C₀ * a ^ 2 * E * S ^ 2, by positivity, ?_⟩
  intro X Y hX hY M hM T hT L y
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXY0 : 0 < X * Y := mul_pos hX0 hY0
  have hXY : 1 ≤ X * Y := by nlinarith
  have haY : 1 ≤ a * Y := by nlinarith
  have hT' : ∀ s ∈ T, A.exteriorNorm s ≤ a * Y := by
    intro s hs
    exact (hT s hs).2.trans (mul_le_mul_of_nonneg_right (le_max_right 1 v1) hY0.le)
  let r : ℤ → A.R → ℂ := fun j m => (Y⁻¹ : ℂ) * ∑ s ∈ T,
    NormalizedProbe.gaussRow A D s m *
      ProbeLogWeight.mode L j (A.exteriorNorm s / Y)
  let B : ℝ := C₀ * (X * Y + (a * Y) ^ 2) * (E / Y)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : ∀ j, (∑ m ∈ M, ‖r j m‖ ^ 2) ≤ B := by
    intro j
    exact (hsieve (X * Y) (a * Y) hXY haY M hM T hT' Y L j).trans
      (mul_le_mul_of_nonneg_left (henergy Y hY L j T hT) (by positivity))
  have hmode : ∀ j, (∑ m ∈ M, ‖c j (y m) * r j m‖ ^ 2) ≤ B * ‖c j‖ ^ 2 := by
    intro j
    calc
      (∑ m ∈ M, ‖c j (y m) * r j m‖ ^ 2) ≤
          ∑ m ∈ M, ‖c j‖ ^ 2 * ‖r j m‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
            (BoundedContinuousFunction.norm_coe_le_norm (c j) (y m))) (sq_nonneg _)
      _ = ‖c j‖ ^ 2 * (∑ m ∈ M, ‖r j m‖ ^ 2) := by rw [Finset.mul_sum]
      _ ≤ ‖c j‖ ^ 2 * B := mul_le_mul_of_nonneg_left (hr j) (sq_nonneg _)
      _ = B * ‖c j‖ ^ 2 := mul_comm _ _
  obtain ⟨hsummable, hbound⟩ := finite_row_minkowski M
    (fun j m => c j (y m) * r j m) (fun j => ‖c j‖) B hB
    (fun j => norm_nonneg _) hc hmode
  have hnorm : ‖(Real.sqrt (X * Y) : ℂ)⁻¹‖ ^ 2 = (X * Y)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hXY0.le]
  have heq (m : A.R) :
      (Y⁻¹ : ℂ) * ∑' j : ℤ, c j (y m) * ∑ s ∈ T,
        NormalizedProbe.gaussRow A D s m *
          ProbeLogWeight.mode L j (A.exteriorNorm s / Y) =
      ∑' j : ℤ, c j (y m) * r j m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [r]
    ring
  simp_rw [heq, norm_mul, mul_pow, hnorm]
  rw [← Finset.mul_sum]
  calc
    (X * Y)⁻¹ * (∑ m ∈ M, ‖∑' j : ℤ, c j (y m) * r j m‖ ^ 2) ≤
        (X * Y)⁻¹ * (B * S ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hXY0.le)
    _ ≤ C₀ * a ^ 2 * E * S ^ 2 * (X * Y)⁻¹ * (X * Y + Y ^ 2) / Y := by
      have hcut : X * Y + (a * Y) ^ 2 ≤ a ^ 2 * (X * Y + Y ^ 2) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ha2) hXY0.le]
      have hh := mul_le_mul_of_nonneg_left hcut
        (show 0 ≤ (X * Y)⁻¹ * C₀ * (E / Y) * S ^ 2 by positivity)
      dsimp [B]
      convert hh using 1 <;> ring

end
end DedekindZetaZeroFree.ProbeCoefficientEnergy

end

section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
noncomputable section
open scoped NumberField Classical BoundedContinuousFunction

variable {F : Type} [Field F] [NumberField F]

def additiveCoefficient (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (X Y : ℝ) (t : A.G1) (m : A.R) : ℂ :=
  (Y⁻¹ : ℂ) * ∑' s : A.Exterior,
    (W1 (A.exteriorNorm s / Y) : ℂ) *
      (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * gaussRow A D s m *
      W0 (sLocalDiagonal F A.Sf (m : F) *
        asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹))

theorem additiveCoefficient_uniform_support (A : SArithmeticData F)
    (Ω : Set A.G1) (hΩ : IsCompact (closure Ω))
    (W0 : SLocalProduct F A.Sf → ℂ) (hW0 : HasCompactSupport W0)
    (hUnits : tsupport W0 ⊆ {x | IsUnit x}) (W1 : ProbeRealAnnularWeight) :
    ∃ K : Set A.G, IsCompact K ∧
      ∀ (X Y : ℝ), 0 < X → 0 < Y →
        Set.Finite (scaledIntegralRows A (X * Y) K) ∧
        ∀ (t : A.G1), t ∈ Ω →
          (∀ (s : A.Exterior) (m : A.R),
            W1 (A.exteriorNorm s / Y) ≠ 0 →
            W0 (sLocalDiagonal F A.Sf (m : F) *
              asLocalPoint A (((t : A.G) *
                radialSection A (A.exteriorNorm s * X))⁻¹)) ≠ 0 →
            m ∈ scaledIntegralRows A (X * Y) K) ∧
          ∀ (D : ComparisonPoissonCoefficientData F A),
            Function.support (additiveCoefficient A D W0 W1 X Y t) ⊆
              scaledIntegralRows A (X * Y) K := by
  obtain ⟨K, hK, hrows⟩ := common_finite_row_support A Ω hΩ W0 hW0 hUnits
    (tsupport (W1 : ℝ → ℝ)) W1.compactSupport W1.support_positive
  refine ⟨K, hK, ?_⟩
  intro X Y hX hY
  obtain ⟨hfinite, hterm⟩ := hrows W1 Set.Subset.rfl X Y hX hY
  refine ⟨hfinite, ?_⟩
  intro t ht
  refine ⟨hterm t ht, ?_⟩
  intro D m hm
  by_contra hout
  apply hm
  unfold additiveCoefficient
  have hz : ∀ s : A.Exterior,
      (W1 (A.exteriorNorm s / Y) : ℂ) *
        (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * gaussRow A D s m *
        W0 (sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) *
            radialSection A (A.exteriorNorm s * X))⁻¹)) = 0 := by
    intro s
    by_cases hw1 : W1 (A.exteriorNorm s / Y) = 0
    · simp [hw1]
    · have hw0 : W0 (sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) *
            radialSection A (A.exteriorNorm s * X))⁻¹)) = 0 := by
        by_contra hw0
        exact hout (hterm t ht s m hw1 hw0)
      exact mul_eq_zero_of_right _ hw0
  simp only [hz, tsum_zero, mul_zero]

theorem additiveCoefficient_square_summable (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (Ω : Set A.G1) (hΩ : IsCompact (closure Ω))
    (W0 : SLocalProduct F A.Sf → ℂ) (hW0 : HasCompactSupport W0)
    (hUnits : tsupport W0 ⊆ {x | IsUnit x}) (W1 : ProbeRealAnnularWeight)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : A.G1) (ht : t ∈ Ω) :
    Summable (fun m : A.R => ‖additiveCoefficient A D W0 W1 X Y t m‖ ^ 2) := by
  obtain ⟨K, _, hrows⟩ := additiveCoefficient_uniform_support A Ω hΩ W0 hW0 hUnits W1
  obtain ⟨hfinite, hsupport⟩ := hrows X Y hX hY
  apply summable_of_finite_support
  apply hfinite.subset
  intro m hm
  apply (hsupport t ht).2 D
  intro hz
  exact hm (by simp [hz])

theorem additiveCoefficient_energy_normalization_le {C X Y : ℝ}
    (hC : 0 ≤ C) (hX : 0 < X) (hY : 0 < Y) (hYX : Y ≤ X) :
    C * (X * Y)⁻¹ * (X * Y + Y ^ 2) / Y ≤ 2 * C / Y := by
  apply (div_le_div_iff_of_pos_right hY).2
  have hxy : 0 < X * Y := mul_pos hX hY
  calc
    C * (X * Y)⁻¹ * (X * Y + Y ^ 2) ≤ C * (X * Y)⁻¹ * (2 * (X * Y)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (inv_nonneg.mpr hxy.le))
      nlinarith [mul_nonneg (sub_nonneg.mpr hYX) hY.le]
    _ = 2 * C := by field_simp; <;> ring

private lemma finiteCharacter_norm_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (d : R) : ‖χ d‖ ≤ 1 := by
  by_cases hd : IsUnit d
  · obtain ⟨u, rfl⟩ := hd
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa using h.le
  · simp [χ.map_nonunit hd]
private lemma normalizedResidueCoefficient_energy {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (Y q : ℝ) (hq : 0 < q)
    (hcard : (Fintype.card R : ℝ) ≤ q) (z : R → ℂ) (hz : ∀ d, ‖z d‖ ≤ 1) :
    (∑ d : R, ‖(Y⁻¹ : ℂ) * (Real.sqrt q : ℂ)⁻¹ * χ d * z d‖ ^ 2) ≤ Y⁻¹ ^ 2 := by
  have hterm (d : R) :
      ‖(Y⁻¹ : ℂ) * (Real.sqrt q : ℂ)⁻¹ * χ d * z d‖ ^ 2 ≤ Y⁻¹ ^ 2 * q⁻¹ := by
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg q)]
    rw [← abs_inv]
    have hn := finiteCharacter_norm_le_one χ d
    have hz0 := norm_nonneg (z d)
    have hn0 := norm_nonneg (χ d)
    have ha : 0 ≤ |Y⁻¹| * (Real.sqrt q)⁻¹ := by positivity
    have hp : ‖χ d‖ * ‖z d‖ ≤ 1 := mul_le_one₀ hn hz0 (hz d)
    have hb : |Y⁻¹| * (Real.sqrt q)⁻¹ * ‖χ d‖ * ‖z d‖ ≤
        |Y⁻¹| * (Real.sqrt q)⁻¹ := by nlinarith
    have he : (|Y⁻¹| * (Real.sqrt q)⁻¹) ^ 2 = Y⁻¹ ^ 2 * q⁻¹ := by
      simp only [mul_pow, sq_abs, inv_pow, Real.sq_sqrt hq.le]
    rw [← he]
    exact pow_le_pow_left₀ (by positivity) hb 2
  calc
    _ ≤ ∑ d : R, Y⁻¹ ^ 2 * q⁻¹ := Finset.sum_le_sum (fun d _ => hterm d)
    _ = (Fintype.card R : ℝ) * (Y⁻¹ ^ 2 * q⁻¹) := by simp
    _ ≤ q * (Y⁻¹ ^ 2 * q⁻¹) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = Y⁻¹ ^ 2 := by field_simp

private lemma gaussResidue_card (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s : A.Exterior) : Nat.card (FiniteTransform.Residue A.R.toSubring (D.generator s)) =
      Ideal.absNorm s.val := by
  change Nat.card (A.R ⧸ Ideal.span {D.generator s}) = _
  rw [(D.generates s).2, A.exteriorResidue_card]

def gaussFrequencyCoefficient (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (Y L : ℝ) (j : ℤ)
    (s : A.Exterior) (d : FiniteTransform.Residue A.R.toSubring (D.generator s)) : ℂ :=
  (Y⁻¹ : ℂ) * (Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ *
    D.character (D.generator s) d * ProbeLogWeight.mode L j (A.exteriorNorm s / Y)

theorem gaussFrequencyCoefficient_square_energy (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (Y L : ℝ) (j : ℤ) (s : A.Exterior) :
    letI := D.finiteResidue (D.generator s) (D.generates s).1
    (∑ d : FiniteTransform.Residue A.R.toSubring (D.generator s),
      ‖gaussFrequencyCoefficient A D Y L j s d‖ ^ 2) ≤ Y⁻¹ ^ 2 := by
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  have hcard : (Fintype.card (FiniteTransform.Residue A.R.toSubring
      (D.generator s)) : ℝ) ≤ A.exteriorNorm s := by
    rw [← Nat.card_eq_fintype_card, gaussResidue_card]
    exact le_rfl
  exact normalizedResidueCoefficient_energy (D.character (D.generator s)) Y
    (A.exteriorNorm s) (A.exteriorNorm_pos s) hcard
    (fun _ => ProbeLogWeight.mode L j (A.exteriorNorm s / Y))
    (fun _ => (ProbeLogWeight.norm_mode _ _ _).le)

def gaussFrequencyEnergy (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (Y L : ℝ) (j : ℤ) (s : A.Exterior) : ℝ :=
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  ∑ d : FiniteTransform.Residue A.R.toSubring (D.generator s),
    ‖gaussFrequencyCoefficient A D Y L j s d‖ ^ 2

theorem gaussFrequencyEnergy_annular_bound (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hv1 : v0 ≤ v1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 1 ≤ Y →
      {s : A.Exterior | v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y}.Finite ∧
      ∀ (L : ℝ) (j : ℤ) (T : Finset A.Exterior),
        (∀ s ∈ T, v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y) →
        (∑ s ∈ T, gaussFrequencyEnergy A D Y L j s) ≤ C / Y := by
  obtain ⟨C, hC, hcount⟩ := ProbeExteriorIdealCount.ideal_count_annulus F A.cS v0 v1 hv0 hv1
  refine ⟨C, hC, ?_⟩
  intro Y hY
  obtain ⟨hfinite, hcard⟩ := hcount Y hY
  refine ⟨hfinite, ?_⟩
  intro L j T hT
  have hsub : (↑T : Set A.Exterior) ⊆
      {s : A.Exterior | v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y} := by
    intro s hs
    exact hT s hs
  have hc : (T.card : ℝ) ≤ C * Y := by
    have hn := Set.ncard_le_ncard hsub hfinite
    rw [Set.ncard_coe_finset] at hn
    change (Nat.card ↥{s : A.Exterior | v0 * Y ≤ A.exteriorNorm s ∧
      A.exteriorNorm s ≤ v1 * Y} : ℝ) ≤ C * Y at hcard
    rw [Nat.card_coe_set_eq] at hcard
    exact (Nat.cast_le.mpr hn).trans hcard
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  calc
    (∑ s ∈ T, gaussFrequencyEnergy A D Y L j s) ≤ ∑ s ∈ T, Y⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact gaussFrequencyCoefficient_square_energy A D Y L j s
    _ = (T.card : ℝ) * Y⁻¹ ^ 2 := by simp
    _ ≤ (C * Y) * Y⁻¹ ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = C / Y := by field_simp; <;> ring

theorem additiveCoefficient_scaled_normalization (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : A.G1) (m : A.R) :
    additiveCoefficient A D W0 W1 X Y t m =
      ((Real.sqrt (X * Y) : ℂ)⁻¹) *
        ((Y⁻¹ : ℂ) * ∑' s : A.Exterior,
          (W1 (A.exteriorNorm s / Y) : ℂ) *
            ((Real.sqrt (A.exteriorNorm s / Y) : ℂ)⁻¹) * gaussRow A D s m *
            W0 (sLocalDiagonal F A.Sf (m : F) *
              asLocalPoint A (((t : A.G) *
                radialSection A (A.exteriorNorm s * X))⁻¹))) := by
  have hsqrt : ∀ s : A.Exterior,
      (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ =
        (Real.sqrt (X * Y) : ℂ)⁻¹ *
          (Real.sqrt (A.exteriorNorm s / Y) : ℂ)⁻¹ := by
    intro s
    have hq : 0 < A.exteriorNorm s := A.exteriorNorm_pos s
    have h1 : Real.sqrt (A.exteriorNorm s * X) =
        Real.sqrt (X * Y) * Real.sqrt (A.exteriorNorm s / Y) := by
      rw [← Real.sqrt_mul (mul_nonneg hX.le hY.le) (A.exteriorNorm s / Y)]
      congr 1
      field_simp
    rw [h1]
    push_cast
    rw [mul_inv]
  have hterm : ∀ s : A.Exterior,
      (W1 (A.exteriorNorm s / Y) : ℂ) *
        (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * gaussRow A D s m *
        W0 (sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) *
            radialSection A (A.exteriorNorm s * X))⁻¹)) =
      ((Real.sqrt (X * Y) : ℂ)⁻¹) *
        ((W1 (A.exteriorNorm s / Y) : ℂ) *
          ((Real.sqrt (A.exteriorNorm s / Y) : ℂ)⁻¹) * gaussRow A D s m *
          W0 (sLocalDiagonal F A.Sf (m : F) *
            asLocalPoint A (((t : A.G) *
              radialSection A (A.exteriorNorm s * X))⁻¹))) := by
    intro s
    rw [hsqrt s]
    ring
  unfold additiveCoefficient
  rw [tsum_congr hterm, tsum_mul_left]
  ring

private lemma asLocalPoint_mul (A : SArithmeticData F) (g h : A.G) :
    asLocalPoint A (g * h) = asLocalPoint A g * asLocalPoint A h := by rfl
private lemma localUnits_point (A : SArithmeticData F) (g : A.G) :
    (ProbeSheet.localUnits A g).val = asLocalPoint A g := by rfl
private lemma radialSection_mul' (A : SArithmeticData F) (T U : ℝ) (hT : 0 < T) (hU : 0 < U) :
    radialSection A (T * U) = radialSection A T * radialSection A U := by
  simp only [radialSection, dif_pos hT, dif_pos hU, dif_pos (mul_pos hT hU)]
  exact A.radialSection_mul T U hT hU
private lemma logweight_argument (A : SArithmeticData F) (q X Y : ℝ)
    (hq : 0 < q) (hX : 0 < X) (hY : 0 < Y) (t : A.G1) (m : A.R) :
    sLocalDiagonal F A.Sf (m : F) *
      asLocalPoint A (((t : A.G) * radialSection A (q * X))⁻¹) =
    (sLocalDiagonal F A.Sf (m : F) *
      asLocalPoint A (((t : A.G) * radialSection A (X * Y))⁻¹)) *
      (ProbeSheet.ell A (q / Y))⁻¹.val := by
  have hqxy : q * X = X * Y * (q / Y) := by field_simp
  rw [hqxy, radialSection_mul' A _ _ (mul_pos hX hY) (div_pos hq hY)]
  simp only [ProbeSheet.ell, dif_pos (div_pos hq hY)]
  rw [← map_inv, localUnits_point]
  rw [← mul_assoc, mul_inv, asLocalPoint_mul]
  simp only [radialSection, dif_pos (div_pos hq hY)]
  ring
private lemma sqrt_neg_half (v : ℝ) (hv : 0 < v) :
    (Real.sqrt v : ℂ)⁻¹ = (v ^ (-(1 / 2 : ℝ)) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.rpow_neg hv.le]

theorem additiveCoefficient_logweight (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : A.G1) (m : A.R) :
    additiveCoefficient A D W0 W1 X Y t m =
      (Real.sqrt (X * Y) : ℂ)⁻¹ * ((Y⁻¹ : ℂ) * ∑' s : A.Exterior,
        gaussRow A D s m * ProbeLogWeight.row A W0 W1 (A.exteriorNorm s / Y)
          (sLocalDiagonal F A.Sf (m : F) *
            asLocalPoint A (((t : A.G) * radialSection A (X * Y))⁻¹))) := by
  rw [additiveCoefficient_scaled_normalization A D W0 W1 X Y hX hY]
  congr 2
  apply tsum_congr
  intro s
  rw [logweight_argument A _ X Y (A.exteriorNorm_pos s) hX hY t m,
    sqrt_neg_half _ (div_pos (A.exteriorNorm_pos s) hY)]
  unfold ProbeLogWeight.row
  ring

theorem additiveCoefficient_logweight_expansion (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (v0 v1 a L : ℝ) (K : Set (SLocalProduct F A.Sf))
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hc : ProbeLogWeight.Separation A W0 W1 v0 v1 a L K c)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : A.G1) (m : A.R) :
    additiveCoefficient A D W0 W1 X Y t m =
      (Real.sqrt (X * Y) : ℂ)⁻¹ * ((Y⁻¹ : ℂ) * ∑' s : A.Exterior,
        gaussRow A D s m * ProbeLogWeight.truncatedSeries A v0 v1 L c
          (A.exteriorNorm s / Y) (sLocalDiagonal F A.Sf (m : F) *
            asLocalPoint A (((t : A.G) * radialSection A (X * Y))⁻¹))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcut, _⟩ := hc
  rw [additiveCoefficient_logweight A D W0 W1 X Y hX hY]
  congr 2
  apply tsum_congr
  intro s
  rw [hcut _ (div_pos (A.exteriorNorm_pos s) hY)]

private lemma finite_mode_exchange (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ) (hc : Summable (fun j => ‖c j‖))
    (L Y : ℝ) (T : Finset A.Exterior) (y : SLocalProduct F A.Sf) (m : A.R) :
    (∑ s ∈ T, gaussRow A D s m *
      ∑' j : ℤ, c j y * ProbeLogWeight.mode L j (A.exteriorNorm s / Y)) =
    ∑' j : ℤ, c j y * ∑ s ∈ T,
      gaussRow A D s m * ProbeLogWeight.mode L j (A.exteriorNorm s / Y) := by
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  · intro s hs
    exact (ProbeLogWeight.summable_norm_modes A c hc L (A.exteriorNorm s / Y) y).of_norm.mul_left _

theorem additiveCoefficient_finite_fourier_exchange (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (v0 v1 a L : ℝ) (K : Set (SLocalProduct F A.Sf))
    (c : ℤ → SLocalProduct F A.Sf →ᵇ ℂ)
    (hc : ProbeLogWeight.Separation A W0 W1 v0 v1 a L K c)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (T : Finset A.Exterior)
    (hT : ∀ s, s ∈ T ↔ A.exteriorNorm s / Y ∈ Set.Icc v0 v1)
    (t : A.G1) (m : A.R) :
    additiveCoefficient A D W0 W1 X Y t m =
      (Real.sqrt (X * Y) : ℂ)⁻¹ * ((Y⁻¹ : ℂ) * ∑' j : ℤ,
        c j (sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) * radialSection A (X * Y))⁻¹)) *
        ∑ s ∈ T, gaussRow A D s m * ProbeLogWeight.mode L j (A.exteriorNorm s / Y)) := by
  have hcnorm := hc.2.2.2.2.2.2.2.2.2.2.2.1
  rw [additiveCoefficient_logweight_expansion A D W0 W1 v0 v1 a L K c hc X Y hX hY]
  congr 2
  rw [tsum_eq_sum (s := T) (fun s hs => ?_)]
  · simp only [ProbeLogWeight.truncatedSeries]
    have hf : ∀ s ∈ T, A.exteriorNorm s / Y ∈ Set.Icc v0 v1 :=
      fun s hs => (hT s).mp hs
    calc
      _ = ∑ s ∈ T, gaussRow A D s m * ∑' j : ℤ,
          c j (sLocalDiagonal F A.Sf (m : F) *
            asLocalPoint A (((t : A.G) * radialSection A (X * Y))⁻¹)) *
          ProbeLogWeight.mode L j (A.exteriorNorm s / Y) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [if_pos (hf s hs)]
      _ = _ := finite_mode_exchange A D c hcnorm L Y T _ m
  · simp [ProbeLogWeight.truncatedSeries, (hT s).not.mp hs]

theorem principal_additiveCoefficient_square_energy (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces) (P : PrincipalData A σ η hS)
    (Ω : Set A.G1) (hΩ : IsCompact (closure Ω)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y : ℝ), 1 ≤ X → 1 ≤ Y →
      ∀ (t : A.G1), t ∈ Ω →
        Summable (fun m : A.R =>
          ‖additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ ^ 2) ∧
        (∑' m : A.R,
          ‖additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ ^ 2) ≤
          C * (X * Y)⁻¹ * (X * Y + Y ^ 2) / Y ∧
        (Y ≤ X → (∑' m : A.R,
          ‖additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ ^ 2) ≤
          2 * C / Y) := by
  obtain ⟨Kbox, hKbox, hsupport⟩ := additiveCoefficient_uniform_support A Ω hΩ
    P.W0 P.compactSupport P.supportUnits P.W1
  obtain ⟨v0, v1, a, L, K, c, hc⟩ := probe_logweight_separation F A P.W0 P.W1
    P.annular P.compactSupport P.supportUnits
  have hv0 : 0 < v0 := hc.1
  have hv1 : v0 ≤ v1 := hc.2.1.le
  have hcnorm : Summable (fun j : ℤ => ‖c j‖) := hc.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨E, hE, hcount⟩ := gaussFrequencyEnergy_annular_bound A P.coefficients
    v0 v1 hv0 hv1
  have hrawenergy : ∀ Y : ℝ, 1 ≤ Y → ∀ (L : ℝ) (j : ℤ) (T : Finset A.Exterior),
      (∀ s ∈ T, v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y) →
      (∑ s ∈ T,
        (letI := P.coefficients.finiteResidue (P.coefficients.generator s)
          (P.coefficients.generates s).1
         ∑ d : FiniteTransform.Residue A.R.toSubring (P.coefficients.generator s),
           ‖(Y⁻¹ : ℂ) * (Real.sqrt (A.exteriorNorm s) : ℂ)⁻¹ *
             P.coefficients.character (P.coefficients.generator s) d *
               ProbeLogWeight.mode L j (A.exteriorNorm s / Y)‖ ^ 2)) ≤ E / Y := by
    intro Y hY L j T hT
    exact (hcount Y hY).2 L j T hT
  obtain ⟨C, hC, hbound⟩ := ProbeCoefficientEnergy.separated_finite_row_energy A
    P.coefficients P.finiteTrace P.continuousTrace P.traceCompatible P.sameTrace
    Kbox hKbox c hcnorm v0 v1 E hE hrawenergy
  refine ⟨C, hC, ?_⟩
  intro X Y hX hY t ht
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  obtain ⟨hMfinite, hsupp⟩ := hsupport X Y hXpos hYpos
  let M : Finset A.R := hMfinite.toFinset
  have hM : (↑M : Set A.R) ⊆ scaledIntegralRows A (X * Y) Kbox := by
    intro m hm
    exact hMfinite.mem_toFinset.mp hm
  let T : Finset A.Exterior := (hcount Y hY).1.toFinset
  have hTann : ∀ s ∈ T, v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y := by
    intro s hs
    exact (hcount Y hY).1.mem_toFinset.mp hs
  have hT : ∀ s, s ∈ T ↔ A.exteriorNorm s / Y ∈ Set.Icc v0 v1 := by
    intro s
    rw [(hcount Y hY).1.mem_toFinset]
    change (v0 * Y ≤ A.exteriorNorm s ∧ A.exteriorNorm s ≤ v1 * Y) ↔
      (v0 ≤ A.exteriorNorm s / Y ∧ A.exteriorNorm s / Y ≤ v1)
    rw [le_div_iff₀ hYpos, div_le_iff₀ hYpos]
  have henergy : (∑' m : A.R,
      ‖additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ ^ 2) ≤
      C * (X * Y)⁻¹ * (X * Y + Y ^ 2) / Y := by
    rw [tsum_eq_sum (s := M) (fun m hm => ?_)]
    · convert hbound X Y hX hY M hM T hTann L
        (fun m => sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) * radialSection A (X * Y))⁻¹)) using 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [additiveCoefficient_finite_fourier_exchange A P.coefficients P.W0 P.W1
        v0 v1 a L K c hc X Y hXpos hYpos T hT t m]
    · have hz : additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m = 0 := by
        apply Function.notMem_support.mp
        intro hnonzero
        exact hm (hMfinite.mem_toFinset.mpr ((hsupp t ht).2 P.coefficients hnonzero))
      simp [hz]
  refine ⟨additiveCoefficient_square_summable A P.coefficients Ω hΩ P.W0
    P.compactSupport P.supportUnits P.W1 X Y hXpos hYpos t ht, henergy, ?_⟩
  intro hYX
  exact henergy.trans (additiveCoefficient_energy_normalization_le hC hXpos hYpos hYX)

end
end NormalizedProbe
end DedekindZetaZeroFree

end
