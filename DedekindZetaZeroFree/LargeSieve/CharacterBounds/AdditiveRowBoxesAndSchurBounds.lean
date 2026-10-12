module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.BandlimitedPoissonGramMajorant

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds
noncomputable section
open scoped Classical ComplexConjugate

private lemma schur_square_expand {κ : Type*} [Fintype κ]
    (w : ℝ) (a b : κ → ℂ) :
    (w * ‖∑ j, b j * a j‖ ^ 2 : ℂ) =
      ∑ j, ∑ k, (b j * conj (b k)) * ((w : ℂ) * a j * conj (a k)) := by
  classical
  push_cast
  rw [← Complex.mul_conj', map_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem weighted_schur_bound {ι κ : Type*} [Fintype κ]
    (rows : Finset ι) (A : ι → κ → ℂ) (w : ι → ℝ)
    (G : Matrix κ κ ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hw : ∀ m, 0 ≤ w m)
    (hrows : ∀ m ∈ rows, 1 ≤ w m)
    (hGram : ∀ j k, HasSum
      (fun m : ι => (w m : ℂ) * A m j * conj (A m k)) (G j k))
    (hkernel : ∀ j, ∑ k, ‖G j k‖ ≤ D)
    (b : κ → ℂ) :
    (∑ m ∈ rows, ‖∑ j, b j * A m j‖ ^ 2) ≤
      D * ∑ j, ‖b j‖ ^ 2 := by
  classical
  change κ → κ → ℂ at G
  have hsymm : ∀ j k, G k j = conj (G j k) := by
    intro j k
    have hc := Complex.hasSum_conj'.mpr (hGram j k)
    have he : (fun m : ι => conj ((w m : ℂ) * A m j * conj (A m k))) =
        (fun m : ι => (w m : ℂ) * A m k * conj (A m j)) := by
      funext m
      simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
      ring
    rw [he] at hc
    exact (hGram k j).unique hc
  have hnormsymm : ∀ j k, ‖G k j‖ = ‖G j k‖ := by
    intro j k
    rw [hsymm, Complex.norm_conj]
  have hs := hasSum_sum (s := Finset.univ) (fun j _ =>
    hasSum_sum (s := Finset.univ) (fun k _ =>
      (hGram j k).mul_left (b j * conj (b k))))
  have hr : HasSum (fun m => w m * ‖∑ j, b j * A m j‖ ^ 2)
      (∑ j, ∑ k, (b j * conj (b k) * G j k)).re := by
    have he : (fun m : ι => ∑ j, ∑ k,
        (b j * conj (b k)) * ((w m : ℂ) * A m j * conj (A m k))) =
        (fun m => (w m * ‖∑ j, b j * A m j‖ ^ 2 : ℂ)) := by
      funext m
      exact (schur_square_expand (w m) (A m) b).symm
    rw [he] at hs
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] using
      Complex.hasSum_re hs
  have hfinite : (∑ j, ∑ k, (b j * conj (b k) * G j k)).re ≤
      D * ∑ j, ‖b j‖ ^ 2 := by
    have hp : ∀ j k, (b j * conj (b k) * G j k).re ≤
        (‖b j‖ ^ 2 * ‖G j k‖ + ‖b k‖ ^ 2 * ‖G j k‖) / 2 := by
      intro j k
      have h := Complex.re_le_norm (b j * conj (b k) * G j k)
      simp only [norm_mul, Complex.norm_conj] at h
      have hy := mul_nonneg (sq_nonneg (‖b j‖ - ‖b k‖)) (norm_nonneg (G j k))
      nlinarith
    have he : (∑ j, ∑ k, ‖b k‖ ^ 2 * ‖G j k‖) =
        ∑ j, ∑ k, ‖b j‖ ^ 2 * ‖G j k‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [hnormsymm]
    calc
      _ = ∑ j, ∑ k, (b j * conj (b k) * G j k).re := by
        change Complex.reCLM (∑ j, ∑ k, b j * conj (b k) * G j k) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact map_sum Complex.reCLM _ _
      _ ≤ ∑ j, ∑ k,
          (‖b j‖ ^ 2 * ‖G j k‖ + ‖b k‖ ^ 2 * ‖G j k‖) / 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.sum_le_sum (fun k hk => hp j k)
      _ = ∑ j, ∑ k, ‖b j‖ ^ 2 * ‖G j k‖ := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib]
        rw [he]
        ring
      _ = ∑ j, ‖b j‖ ^ 2 * ∑ k, ‖G j k‖ := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ j, ‖b j‖ ^ 2 * D := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hkernel j) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  calc
    _ ≤ ∑ m ∈ rows, w m * ‖∑ j, b j * A m j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact le_mul_of_one_le_left (sq_nonneg _) (hrows m hm)
    _ ≤ ∑' m, w m * ‖∑ j, b j * A m j‖ ^ 2 :=
      hr.summable.sum_le_tsum rows (fun m _ => mul_nonneg (hw m) (sq_nonneg _))
    _ = _ := hr.tsum_eq
    _ ≤ _ := hfinite

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds

end

section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain NumberField

namespace ProbeAdditive
variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def archPhase (x : InfiniteAdeleRing F) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    ((∑ v : InfinitePlace F, 2 * (NumberField.InfinitePlace.Completion.extensionEmbedding v (x v)).re) : ℂ))

def phase (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (x : SLocalProduct F S) : ℂ :=
  archPhase F x.1 * ∏ v : ↥S, (e v (x.2 v) : ℂ)

def TraceCompatible (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle) : Prop :=
  ∀ m : sIntegerRing F S, phase F S e (sIntegerDiagonal F S m) = 1

def balancedDilation (N : ℝ) : SLocalProduct F S :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (N ^ (1 / (Module.finrank ℚ F : ℝ)) • (1 : mixedEmbedding.mixedSpace F)), 1)

def boxRows (N : ℝ) (K : Set (SLocalProduct F S)) : Set (ProbeSeparation.Integers F S) :=
  {m | sLocalDiagonal F S (m : F) ∈ (fun x => balancedDilation F S N * x) '' K}

open scoped ComplexConjugate

lemma archPhase_neg (F : Type) [Field F] [NumberField F]
    (x : InfiniteAdeleRing F) : archPhase F (-x) = conj (archPhase F x) := by
  unfold archPhase
  rw [← Complex.exp_conj]
  congr 1
  have hx : ∀ v : InfinitePlace F,
      (InfinitePlace.Completion.extensionEmbedding v ((-x) v)).re =
        -(InfinitePlace.Completion.extensionEmbedding v (x v)).re := by
    intro v
    change (InfinitePlace.Completion.extensionEmbedding v (-(x v))).re = _
    simp
  simp only [hx, mul_neg, Finset.sum_neg_distrib, Complex.ofReal_neg,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [map_sum, map_mul, Complex.conj_ofReal, map_ofNat]
  ring
lemma phase_neg (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x : SLocalProduct F S) : phase F S e (-x) = conj (phase F S e x) := by
  unfold phase
  change archPhase F (-x.1) * (∏ v : S, (e v (-(x.2 v)) : ℂ)) =
    conj (archPhase F x.1 * ∏ v : S, (e v (x.2 v) : ℂ))
  rw [map_mul, archPhase_neg, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  change ((e v (-(x.2 v)) : Circle) : ℂ) = _
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

lemma matrix_dual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ b : κ → ℂ, (∑ i, ‖∑ j, b j * A i j‖ ^ 2) ≤ B * ∑ j, ‖b j‖ ^ 2) :
    ∀ a : ι → ℂ, (∑ j, ‖∑ i, a i * conj (A i j)‖ ^ 2) ≤ B * ∑ i, ‖a i‖ ^ 2 := by
  classical
  let T := A.toEuclideanLin.toContinuousLinearMap
  have heval (b : EuclideanSpace ℂ κ) (i : ι) :
      (T b) i = ∑ j, b j * A i j := by
    simp [T, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, mul_comm]
  have hnorm (b : EuclideanSpace ℂ κ) : ‖T b‖ ^ 2 ≤ B * ‖b‖ ^ 2 := by
    simpa only [EuclideanSpace.norm_sq_eq, heval] using h b.ofLp
  have hT : ‖T‖ ≤ Real.sqrt B := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg _)
    intro b
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hB]
    exact hnorm b
  intro a
  let u : EuclideanSpace ℂ ι := WithLp.toLp 2 a
  have hd := (ContinuousLinearMap.adjoint T).le_opNorm u
  rw [ContinuousLinearMap.adjoint.norm_map] at hd
  have hd' : ‖ContinuousLinearMap.adjoint T u‖ ≤ Real.sqrt B * ‖u‖ :=
    hd.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hd' 2
  rw [mul_pow, Real.sq_sqrt hB] at hsq
  have hadj : ContinuousLinearMap.adjoint T = A.conjTranspose.toEuclideanLin.toContinuousLinearMap := by
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [hadj] at hsq
  simpa [EuclideanSpace.norm_sq_eq, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose, u, mul_comm] using hsq

lemma archPhase_add (F : Type) [Field F] [NumberField F]
    (x y : InfiniteAdeleRing F) : archPhase F (x + y) = archPhase F x * archPhase F y := by
  unfold archPhase
  rw [← Complex.exp_add]
  congr 1
  have hadd : ∀ v : InfinitePlace F,
      (InfinitePlace.Completion.extensionEmbedding v ((x + y) v)).re =
        (InfinitePlace.Completion.extensionEmbedding v (x v)).re +
          (InfinitePlace.Completion.extensionEmbedding v (y v)).re := by
    intro v
    change (InfinitePlace.Completion.extensionEmbedding v (x v + y v)).re = _
    simp
  simp only [hadd, mul_add, Finset.sum_add_distrib, Complex.ofReal_add]
lemma phase_add (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (x y : SLocalProduct F S) : phase F S e (x + y) = phase F S e x * phase F S e y := by
  unfold phase
  change archPhase F (x.1 + y.1) * (∏ v : S, (e v (x.2 v + y.2 v) : ℂ)) = _
  simp only [archPhase_add, AddChar.map_add_eq_mul, Circle.coe_mul, Finset.prod_mul_distrib]
  ring

end ProbeAdditive

 instance infiniteAdeleT2 (F : Type) [Field F] [NumberField F] :
    T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
 def localSize (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SLocalProduct F S) : ℝ :=
  (∏ v : InfinitePlace F, ‖x.1 v‖ ^ v.mult) * ∏ v : S, ‖x.2 v‖
private lemma localSize_continuous (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (localSize F S) := by
  unfold localSize
  fun_prop
private lemma localSize_diagonal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (m : F) :
    localSize F S (sLocalDiagonal F S m) = ProbeSeparation.productNorm F S m := by
  unfold localSize ProbeSeparation.productNorm
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    rw [sLocalDiagonal_infinite]
    change ‖((WithAbs.equiv v.1).symm m : v.Completion)‖ ^ v.mult = _
    rw [InfinitePlace.Completion.norm_coe]
    rfl
  · simp only [sLocalDiagonal_finite, FinitePlace.mk_apply]
    exact Finset.prod_coe_sort S (fun v => ‖algebraMap F (v.adicCompletion F) m‖)
private lemma localSize_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : localSize F S 0 = 0 := by
  unfold localSize
  have : ∀ v : InfinitePlace F, (0:ℝ) ^ v.mult = 0 := by
    intro v
    exact zero_pow (by have := v.mult_pos; omega)
  change (∏ v : InfinitePlace F, ‖(0 : v.Completion)‖ ^ v.mult) * _ = 0
  simp [this]
private lemma diagonal_injective (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Function.Injective (sIntegerDiagonal F S) := by
  exact (RingHom.injective (sLocalDiagonal F S)).comp Subtype.val_injective
private lemma diagonal_discrete (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsDiscrete ((sIntegerDiagonal F S).toAddMonoidHom.range : Set (SLocalProduct F S)) := by
  let G := (sIntegerDiagonal F S).toAddMonoidHom.range
  letI : IsTopologicalAddGroup G := inferInstance
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_of_isOpen_singleton_zero
  apply isOpen_induced_iff.mpr
  refine ⟨{x | localSize F S x < 1}, isOpen_lt (localSize_continuous F S) continuous_const, ?_⟩
  ext x
  change localSize F S x.val < 1 ↔ x = 0
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := x.property
    change sIntegerDiagonal F S m = x.val at hm
    have hm0 : m = 0 := by
      by_contra hm0
      have hl := probe_sinteger_product_norm_lower_bound F S m hm0
      rw [← localSize_diagonal F S] at hl
      change 1 ≤ localSize F S (sIntegerDiagonal F S m) at hl
      rw [hm] at hl
      exact (not_lt_of_ge hl) hx
    apply Subtype.ext
    simpa [hm0] using hm.symm
  · rintro rfl
    rw [show ((0 : G) : SLocalProduct F S) = 0 from rfl, localSize_zero]
    norm_num

theorem probe_additive_box_rows_finite (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℝ)
    (K : Set (SLocalProduct F S)) (hK : IsCompact K) :
    (ProbeAdditive.boxRows F S N K).Finite := by
  let G := (sIntegerDiagonal F S).toAddMonoidHom.range
  let L := (fun x => ProbeAdditive.balancedDilation F S N * x) '' K
  have hL : IsCompact L := hK.image (continuous_const.mul continuous_id)
  have hG : IsDiscrete (G : Set (SLocalProduct F S)) := diagonal_discrete F S
  have hfinite : (L ∩ (G : Set (SLocalProduct F S))).Finite :=
    (hL.inter_right (G.isClosed_of_isDiscrete hG)).finite (hG.mono Set.inter_subset_right)
  have hf := hfinite.preimage (diagonal_injective F S).injOn
  change (ProbeAdditive.boxRows F S N K).Finite
  apply hf.subset
  intro m hm
  exact ⟨hm, ⟨m, rfl⟩⟩

open scoped ComplexConjugate

theorem probe_additive_row_box_sieve (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : ↥S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v)) (htrace : ProbeAdditive.TraceCompatible F S e)
    (K : Set (SLocalProduct F S)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N V : ℝ), 1 ≤ N → 1 ≤ V →
      ∀ (p : ProbeSeparation.Presentation F S)
        (P : Finset (ProbeSeparation.ReducedPair F S)),
        (∀ α ∈ P, ProbeSeparation.denominatorNorm F α ≤ V) →
        (let rows := (probe_additive_box_rows_finite F S N K hK).toFinset
         (∀ b : ↥P → ℂ,
           (∑ m : ↥rows, ‖∑ α : ↥P, b α * ProbeAdditive.phase F S e
             (sLocalDiagonal F S ((m.val : F) * ProbeSeparation.value F p α.val))‖ ^ 2) ≤
             C * (N + V ^ 2) * ∑ α : ↥P, ‖b α‖ ^ 2) ∧
         (∀ a : ↥rows → ℂ,
           (∑ α : ↥P, ‖∑ m : ↥rows, a m * ProbeAdditive.phase F S e
             (sLocalDiagonal F S (-((m.val : F) * ProbeSeparation.value F p α.val)))‖ ^ 2) ≤
             C * (N + V ^ 2) * ∑ m : ↥rows, ‖a m‖ ^ 2)) := by
  suffices hforward : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N V : ℝ), 1 ≤ N → 1 ≤ V →
      ∀ (p : ProbeSeparation.Presentation F S)
        (P : Finset (ProbeSeparation.ReducedPair F S)),
        (∀ α ∈ P, ProbeSeparation.denominatorNorm F α ≤ V) →
        (let rows := (probe_additive_box_rows_finite F S N K hK).toFinset
         ∀ b : ↥P → ℂ,
           (∑ m : ↥rows, ‖∑ α : ↥P, b α * ProbeAdditive.phase F S e
             (sLocalDiagonal F S ((m.val : F) * ProbeSeparation.value F p α.val))‖ ^ 2) ≤
             C * (N + V ^ 2) * ∑ α : ↥P, ‖b α‖ ^ 2) by
    obtain ⟨C, hC, hforward⟩ := hforward
    refine ⟨C, hC, ?_⟩
    intro N V hN hV p P hP
    let rows := (probe_additive_box_rows_finite F S N K hK).toFinset
    let A : Matrix (↥rows) (↥P) ℂ :=
      fun m α => ProbeAdditive.phase F S e
        (sLocalDiagonal F S ((m.val : F) * ProbeSeparation.value F p α.val))
    have hB : 0 ≤ C * (N + V ^ 2) := mul_nonneg hC (by nlinarith [sq_nonneg V])
    have hrow : ∀ b : ↥P → ℂ,
        (∑ m : ↥rows, ‖∑ α : ↥P, b α * A m α‖ ^ 2) ≤
          C * (N + V ^ 2) * ∑ α : ↥P, ‖b α‖ ^ 2 := by
      simpa only [A, rows] using hforward N V hN hV p P hP
    dsimp only
    constructor
    · exact hrow
    · intro a
      have hd := ProbeAdditive.matrix_dual A (C * (N + V ^ 2)) hB hrow a
      convert hd using 1
      apply Finset.sum_congr rfl
      intro α hα
      apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
      apply Finset.sum_congr rfl
      intro m hm
      congr 1
      simpa only [A, map_neg] using
        (ProbeAdditive.phase_neg F S e
          (sLocalDiagonal F S ((m.val : F) * ProbeSeparation.value F p α.val)))
  obtain ⟨C, hC, hmajorant⟩ := ProbeAdditiveGramBounds.arithmetic_majorant_gram
    F ζ12 hζ12 S e he (ProbeAdditive.phase F S e) (fun x => rfl)
    htrace (ProbeAdditive.balancedDilation F S) (fun N => rfl) K hK
  refine ⟨C, hC, ?_⟩
  intro N V hN hV p P hP
  obtain ⟨Φ, hcont, hpos, hmajor, hgrams⟩ := hmajorant N V hN hV
  obtain ⟨G, hGram, hkernel⟩ := hgrams p P hP
  let rows := (probe_additive_box_rows_finite F S N K hK).toFinset
  let A : ProbeSeparation.Integers F S → ↥P → ℂ := fun m α =>
    ProbeAdditive.phase F S e
      (sLocalDiagonal F S ((m : F) * ProbeSeparation.value F p α.val))
  let w : ProbeSeparation.Integers F S → ℝ := fun m =>
    Φ (sLocalDiagonal F S (m : F))
  have hB : 0 ≤ C * (N + V ^ 2) :=
    mul_nonneg hC (by nlinarith [sq_nonneg V])
  dsimp only
  intro b
  have hh := ProbeAdditiveGramBounds.weighted_schur_bound rows A w G
    (C * (N + V ^ 2)) hB (fun m => hpos _)
    (fun m hm => hmajor _ (by
      change m ∈ ProbeAdditive.boxRows F S N K
      simpa only [rows, Set.Finite.mem_toFinset] using hm))
    hGram hkernel b
  rw [← Finset.sum_coe_sort rows] at hh
  exact hh

end
end DedekindZetaZeroFree

end
