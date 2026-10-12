module

public import DedekindZetaZeroFree.Metaplectic.Kubota.PGL.LocalCover

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPRankOneCartanGeometry

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (w : HeightOneSpectrum (𝓞 F))

local instance baseGroup : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr w)) :=
  @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr w))
    (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w))

local instance : ValuativeRel (KPLocalCube.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w

local instance : IsNonarchimedeanLocalField (KPLocalCube.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w

def K0 : Subgroup (KPPGLLocalCover.LocalPGL2 F (Sum.inr w)) :=
  ((KPPGLLocalCover.baseQuotient F (Sum.inr w)).comp
    (KPTameCompact.inclusion F w)).range

def coveredK0 : Subgroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) :=
  (K0 F w).comap (KPPGLLocalCover.projection F ζ hζ (Sum.inr w))

def diagonalLift (π : (w.adicCompletion F)ˣ) (n : ℕ) :
    KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w) :=
  KPPGLLocalCover.A F ζ hζ (Sum.inr w) (π ^ n)

def doubleCoset (π : (w.adicCompletion F)ˣ) (n : ℕ) :
    Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) :=
  {g | ∃ k₁ k₂ : coveredK0 F ζ hζ w,
    g = k₁.val * diagonalLift F ζ hζ w π n * k₂.val}

def cartanTruncation (π : (w.adicCompletion F)ˣ) (M : ℕ) :
    Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) :=
  ⋃ n ≤ M, doubleCoset F ζ hζ w π n

theorem finite_kernel_proper {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G]
    (p : G →* H) (hp : IsLocalHomeomorph p) (hs : Function.Surjective p)
    (hf : ∀ y : H, (p ⁻¹' {y}).Finite) : IsProperMap p := by
  have hq := hp.isOpenMap.isQuotientMap hp.continuous hs
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hp.continuous, ?_, fun y => (hf y).isCompact⟩
  intro S hS
  apply (hq.isClosed_preimage).mp
  have he : p ⁻¹' (p '' S) = ⋃ k ∈ (p ⁻¹' {1}), (fun x : G => x * k) '' S := by
    ext x
    constructor
    · rintro ⟨s, hs, he⟩
      apply Set.mem_iUnion₂.mpr
      refine ⟨s⁻¹ * x, ?_, s, hs, ?_⟩
      · simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, map_inv, he, inv_mul_cancel]
      · simp
    · intro hx
      obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_iUnion₂.mp hx
      refine ⟨s, hs, ?_⟩
      have hk' : p k = 1 := hk
      simp [hk']
  rw [he]
  exact (hf 1).isClosed_biUnion fun k _ => isClosedMap_mul_right k S hS

theorem coveredK0_compact_open (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
    IsCompact (↑(coveredK0 F ζ hζ w) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w))) ∧
      IsOpen (↑(coveredK0 F ζ hζ w) : Set (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w))) := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
  have ht := KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm
  letI := ht.2.2.1
  letI : ValuativeRel (KPTameCompact.K F w) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F w
  letI : IsNonarchimedeanLocalField (KPTameCompact.K F w) :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w
  letI : CompactSpace (KPTameCompact.O F w) := inferInstance
  letI : CompactSpace (Matrix (Fin 2) (Fin 2) (KPTameCompact.O F w)) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → KPTameCompact.O F w))
  letI : CompactSpace (KPTameCompact.K0 F w) := inferInstance
  have hi : Topology.IsOpenEmbedding (KPTameCompact.O F w).subtype :=
    (ValuativeRel.valuation (KPTameCompact.K F w)).isOpen_integer.isOpenEmbedding_subtypeVal
  have hc : Continuous (KPTameCompact.inclusion F w) := hi.continuous.generalLinearGroup_map
  have ho : IsOpenMap (KPTameCompact.inclusion F w) :=
    Units.isOpenMap_map hi.matrix_map.injective hi.matrix_map.isOpenMap
  have hqc : Continuous (KPPGLLocalCover.baseQuotient F (Sum.inr w)) :=
    QuotientGroup.continuous_mk
  have hqo : IsOpenMap (KPPGLLocalCover.baseQuotient F (Sum.inr w)) :=
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap
  have hKc : IsCompact (↑(K0 F w) : Set (KPPGLLocalCover.LocalPGL2 F (Sum.inr w))) := by
    change IsCompact (Set.range ((KPPGLLocalCover.baseQuotient F (Sum.inr w)).comp
      (KPTameCompact.inclusion F w)))
    exact isCompact_range (hqc.comp hc)
  have hKo : IsOpen (↑(K0 F w) : Set (KPPGLLocalCover.LocalPGL2 F (Sum.inr w))) := by
    change IsOpen (Set.range ((KPPGLLocalCover.baseQuotient F (Sum.inr w)).comp
      (KPTameCompact.inclusion F w)))
    rw [← Set.image_univ]
    exact (hqo.comp ho) _ isOpen_univ
  have hf (y : KPPGLLocalCover.LocalPGL2 F (Sum.inr w)) :
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr w) ⁻¹' {y}).Finite := by
    change Set.Finite {x : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w) |
      KPPGLLocalCover.projection F ζ hζ (Sum.inr w) x = y}
    haveI := Nat.finite_of_card_ne_zero (ht.2.2.2.2 y ▸ (by decide : (3 : ℕ) ≠ 0))
    exact Set.toFinite _
  have hp := finite_kernel_proper (KPPGLLocalCover.projection F ζ hζ (Sum.inr w))
    ht.2.2.2.1 (KPPGLLocalCover.projection_surjective F ζ hζ (Sum.inr w)) hf
  exact ⟨hp.isCompact_preimage hKc, hKo.preimage ht.2.2.2.1.continuous⟩

local instance cartanValuativeRel : ValuativeRel (w.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w
local instance cartanValuationCompatible :
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _

private theorem mem_integer_valuation (x : w.adicCompletion F) :
    x ∈ KPTameCompact.O F w ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact ((ValuativeRel.isEquiv (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))
    (ValuativeRel.valuation (w.adicCompletion F))).le_iff_le (x := x) (y := 1)).symm.trans (by simp)
theorem nonzero_integer_unit_times_uniformizer_pow (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (x : w.adicCompletion F) (hx : x ≠ 0) (hv : Valued.v x ≤ 1) :
    ∃ n : ℕ, ∃ u : (KPTameCompact.O F w)ˣ,
      x = (u.val : w.adicCompletion F) * (π.val ^ n) := by
  let v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  have hnz : v x ≠ 0 := v.ne_zero_iff.mpr hx
  let e : ℤ := (v x).log
  have he : v x = WithZero.exp e := (WithZero.exp_log hnz).symm
  have he0 : e ≤ 0 := by
    have hv' : v x ≤ 1 := hv
    simpa only [he, ← WithZero.exp_zero, WithZero.exp_le_exp] using hv'
  let n := (-e).toNat
  have hn : (n : ℤ) = -e := Int.toNat_of_nonneg (neg_nonneg.mpr he0)
  have hp : v (π.val ^ n) = WithZero.exp e := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp [nsmul_eq_mul, hn]
  let t := x / π.val ^ n
  have ht : v t = 1 := by
    dsimp [t]
    rw [v.map_div, he, hp, div_self WithZero.exp_ne_zero]
  have hti : v t⁻¹ = 1 := by rw [map_inv₀, ht, inv_one]
  have htn : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    exact zero_ne_one ht
  let u : (KPTameCompact.O F w)ˣ :=
    { val := ⟨t, (mem_integer_valuation F w t).mpr ht.le⟩
      inv := ⟨t⁻¹, (mem_integer_valuation F w t⁻¹).mpr hti.le⟩
      val_inv := by apply Subtype.ext; change t * t⁻¹ = 1; exact mul_inv_cancel₀ htn
      inv_val := by apply Subtype.ext; change t⁻¹ * t = 1; exact inv_mul_cancel₀ htn }
  exact ⟨n, u, (div_mul_cancel₀ x (pow_ne_zero n π.ne_zero)).symm⟩

private theorem pivot_data (g : KPLocalCover.LocalGL2 F (Sum.inr w))
    (hmax : ∀ i j : Fin 2, Valued.v (g i j) ≤ Valued.v (g 0 0)) :
    g 0 0 ≠ 0 ∧
      Valued.v (g 0 1 / g 0 0) ≤ 1 ∧ Valued.v (g 1 0 / g 0 0) ≤ 1 ∧
      g 1 1 / g 0 0 - (g 1 0 / g 0 0) * (g 0 1 / g 0 0) ≠ 0 ∧
      Valued.v (g 1 1 / g 0 0 - (g 1 0 / g 0 0) * (g 0 1 / g 0 0)) ≤ 1 := by
  let v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  have ha : g 0 0 ≠ 0 := by
    intro ha
    have hz (i j : Fin 2) : g i j = 0 := by
      apply v.map_eq_zero_iff.mp
      apply le_antisymm
      · simpa [ha] using hmax i j
      · exact zero_le
    apply Matrix.GeneralLinearGroup.det_ne_zero g
    simp [Matrix.det_fin_two, hz]
  have hdiv (i j : Fin 2) : v (g i j / g 0 0) ≤ 1 := by
    rw [v.map_div, div_le_one₀ (v.pos_iff.mpr ha)]
    exact hmax i j
  have hx : g 1 1 / g 0 0 - (g 1 0 / g 0 0) * (g 0 1 / g 0 0) ≠ 0 := by
    intro hx
    have hdet : (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)).det = 0 := by
      rw [Matrix.det_fin_two]
      field_simp [ha] at hx
      linear_combination hx
    exact Matrix.GeneralLinearGroup.det_ne_zero g hdet
  refine ⟨ha, hdiv 0 1, hdiv 1 0, hx, ?_⟩
  apply (v.map_sub _ _).trans
  apply max_le (hdiv 1 1)
  rw [map_mul]
  exact mul_le_one₀ (hdiv 1 0) zero_le (hdiv 0 1)
private theorem pivot_factor (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (g : KPLocalCover.LocalGL2 F (Sum.inr w))
    (hmax : ∀ i j : Fin 2, Valued.v (g i j) ≤ Valued.v (g 0 0)) :
    ∃ n : ℕ, ∃ l r : KPTameCompact.K0 F w,
      KPPGLLocalCover.baseQuotient F (Sum.inr w) g =
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w l) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w)
          (KubotaRankTwo.d (w.adicCompletion F) (π ^ n) 1) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w r) := by
  obtain ⟨ha, hb, hc, hx, hvx⟩ := pivot_data F w g hmax
  let b : KPTameCompact.O F w := ⟨g 0 1 / g 0 0, (mem_integer_valuation F w _).mpr hb⟩
  let c : KPTameCompact.O F w := ⟨g 1 0 / g 0 0, (mem_integer_valuation F w _).mpr hc⟩
  let x := g 1 1 / g 0 0 - (g 1 0 / g 0 0) * (g 0 1 / g 0 0)
  obtain ⟨n, u, hu⟩ := nonzero_integer_unit_times_uniformizer_pow F w π hπ x hx hvx
  let W := KPStandardLocalRootLifts.integralW F w
  let l := KPStandardLocalRootLifts.integralLowerN F w c * W *
    KPStandardLocalRootLifts.integralA F w u
  let r := W * KPStandardLocalRootLifts.integralN F w b
  let a : (w.adicCompletion F)ˣ := Units.mk0 (g 0 0) ha
  have he : g = KPScalarSplitCentral.scalarMatrix F (Sum.inr w) a *
      KPTameCompact.inclusion F w l * KubotaRankTwo.d (w.adicCompletion F) (π ^ n) 1 *
      KPTameCompact.inclusion F w r := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [l, r, W, KPTameCompact.inclusion, KPLocalCube.integerInclusion, KPStandardLocalRootLifts.integralLowerN, KPStandardLocalRootLifts.integralN,
        KPStandardLocalRootLifts.integralA, KPStandardLocalRootLifts.integralW,
        KPScalarSplitCentral.scalarMatrix, Matrix.GeneralLinearGroup.map_apply, map_mul,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mk'',
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, KubotaRankTwo.coe_d,
        a, b, c, Units.val_pow_eq_pow_val, ← hu]
    all_goals dsimp [x] at *; field_simp [ha] at hu ⊢ <;> first | assumption | linear_combination hu | ring
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  have hs : KPPGLLocalCover.baseQuotient F (Sum.inr w)
      (KPScalarSplitCentral.scalarMatrix F (Sum.inr w) a) = 1 := by
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
  refine ⟨n, l, r, ?_⟩
  rw [he, map_mul, map_mul, map_mul, hs, one_mul]
private theorem unpermute_factor (π : (w.adicCompletion F)ˣ)
    (g : KPLocalCover.LocalGL2 F (Sum.inr w)) (L R : KPTameCompact.K0 F w)
    (h : ∃ n : ℕ, ∃ l r : KPTameCompact.K0 F w,
      KPPGLLocalCover.baseQuotient F (Sum.inr w)
        (KPTameCompact.inclusion F w L * g * KPTameCompact.inclusion F w R) =
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w l) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w)
          (KubotaRankTwo.d (w.adicCompletion F) (π ^ n) 1) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w r)) :
    ∃ n : ℕ, ∃ l r : KPTameCompact.K0 F w,
      KPPGLLocalCover.baseQuotient F (Sum.inr w) g =
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w l) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w)
          (KubotaRankTwo.d (w.adicCompletion F) (π ^ n) 1) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w r) := by
  obtain ⟨n, l, r, h⟩ := h
  refine ⟨n, L⁻¹ * l, r * R⁻¹, ?_⟩
  simp only [map_mul, map_inv] at h ⊢
  calc
    _ = (KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w L))⁻¹ *
      (KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w L) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w) g *
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w R)) *
      (KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w R))⁻¹ := by group
    _ = _ := by rw [h]; group
theorem ordinary_matrix_cartan_factorization (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (g : KPLocalCover.LocalGL2 F (Sum.inr w)) :
    ∃ n : ℕ, ∃ l r : KPTameCompact.K0 F w,
      KPPGLLocalCover.baseQuotient F (Sum.inr w) g =
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w l) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w)
          (KubotaRankTwo.d (w.adicCompletion F) (π ^ n) 1) *
        KPPGLLocalCover.baseQuotient F (Sum.inr w) (KPTameCompact.inclusion F w r) := by
  obtain ⟨⟨i,j⟩, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin 2 × Fin 2)) (fun p => Valued.v (g p.1 p.2)) (by simp)
  have hmax' (a b : Fin 2) : Valued.v (g a b) ≤ Valued.v (g i j) := hmax (a,b) (by simp)
  let W := KPStandardLocalRootLifts.integralW F w
  have entry (a b : Fin 2) : KPTameCompact.inclusion F w W a b =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) a b := by
    fin_cases a <;> fin_cases b <;>
      simp [W, KPStandardLocalRootLifts.integralW, KPTameCompact.inclusion,
        KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j
  · exact pivot_factor F w π hπ g hmax'
  · apply unpermute_factor F w π g 1 W
    apply pivot_factor F w π hπ
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 0 0
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 0 1
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 1 0
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 1 1
  · apply unpermute_factor F w π g W 1
    apply pivot_factor F w π hπ
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 0 0
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 0 1
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 1 0
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 1 1
  · apply unpermute_factor F w π g W W
    apply pivot_factor F w π hπ
    intro a b
    fin_cases a <;> fin_cases b <;>
      first
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 0 0
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 0 1
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 1 0
      | simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, entry] using hmax' 1 1

theorem lift_projected_factorization (π : (w.adicCompletion F)ˣ) (n : ℕ)
    (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w))
    (b₁ b₂ : K0 F w)
    (hg : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g =
      b₁.val * KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
        (diagonalLift F ζ hζ w π n) * b₂.val) :
    ∃ k₁ k₂ : coveredK0 F ζ hζ w,
      g = k₁.val * diagonalLift F ζ hζ w π n * k₂.val := by
  obtain ⟨k, hk⟩ := KPPGLLocalCover.projection_surjective F ζ hζ (Sum.inr w) b₁.val
  have hk₁ : k ∈ coveredK0 F ζ hζ w := by
    change KPPGLLocalCover.projection F ζ hζ (Sum.inr w) k ∈ K0 F w
    rw [hk]
    exact b₁.property
  let k' := (diagonalLift F ζ hζ w π n)⁻¹ * k⁻¹ * g
  have hk' : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) k' = b₂.val := by
    dsimp [k']
    rw [map_mul, map_mul, map_inv, map_inv, hk, hg]
    group
  have hk₂ : k' ∈ coveredK0 F ζ hζ w := by
    change KPPGLLocalCover.projection F ζ hζ (Sum.inr w) k' ∈ K0 F w
    rw [hk']
    exact b₂.property
  refine ⟨⟨k, hk₁⟩, ⟨k', hk₂⟩, ?_⟩
  dsimp [k']
  group

theorem cartan_decomposition (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) :
    ∃ n : ℕ, ∃ k₁ k₂ : coveredK0 F ζ hζ w,
      g = k₁.val * diagonalLift F ζ hζ w π n * k₂.val := by
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g)
  obtain ⟨n, l, r, h⟩ := ordinary_matrix_cartan_factorization F w π hπ G
  let b₁ : K0 F w := ⟨KPPGLLocalCover.baseQuotient F (Sum.inr w)
    (KPTameCompact.inclusion F w l), ⟨l, rfl⟩⟩
  let b₂ : K0 F w := ⟨KPPGLLocalCover.baseQuotient F (Sum.inr w)
    (KPTameCompact.inclusion F w r), ⟨r, rfl⟩⟩
  refine ⟨n, ?_⟩
  apply lift_projected_factorization F ζ hζ w π n g b₁ b₂
  rw [← hG]
  exact h

theorem cartanTruncation_compact (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (π : (w.adicCompletion F)ˣ) (M : ℕ) :
    letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
    IsCompact (cartanTruncation F ζ hζ w π M) := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hK := (coveredK0_compact_open F ζ hζ w m hm).1
  have hd (n : ℕ) : IsCompact (doubleCoset F ζ hζ w π n) := by
    have he : doubleCoset F ζ hζ w π n =
        (fun p => p.1 * diagonalLift F ζ hζ w π n * p.2) ''
          ((↑(coveredK0 F ζ hζ w) : Set _) ×ˢ ↑(coveredK0 F ζ hζ w)) := by
      ext g
      constructor
      · rintro ⟨k₁, k₂, rfl⟩
        exact ⟨(k₁.val, k₂.val), ⟨k₁.property, k₂.property⟩, rfl⟩
      · rintro ⟨⟨k₁, k₂⟩, ⟨hk₁, hk₂⟩, rfl⟩
        exact ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, rfl⟩
    rw [he]
    exact (hK.prod hK).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  exact (Set.finite_le_nat M).isCompact_biUnion (fun n _ => hd n)

end
end DedekindZetaZeroFree.KPRankOneCartanGeometry
