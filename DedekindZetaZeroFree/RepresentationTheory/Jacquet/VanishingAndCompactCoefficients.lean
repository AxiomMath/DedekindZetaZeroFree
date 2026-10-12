module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RankOne.CartanDecomposition
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ContinuousTwistedRootCoinvariants
public import DedekindZetaZeroFree.Metaplectic.Kubota.BruhatLiftsAndScalarQuotients

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain Topology Filter

namespace DedekindZetaZeroFree.KPRankOneJacquetZeroCompactCoefficients

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (w : HeightOneSpectrum (𝓞 F))

def upperRoot : Multiplicative (KPHilbert.Completion F (Sum.inr w)) →*
    KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w) :=
  (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr w)).comp
    (KPStandardLocalRootLifts.N_hom F ζ hζ (Sum.inr w))

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) V)

abbrev UpperJacquet := RootCoinvariants ρ (upperRoot F ζ hζ w) 1

def coefficient (ℓ : Module.Dual ℂ V) (v : V) :
    KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w) → ℂ :=
  fun g => ℓ (ρ g v)

private theorem mat_eq (t : KPHilbert.Completion F (Sum.inr w)) :
    KPStandardLocalRootLifts.weylSwap _ * KubotaRankTwo.n _ t =
    KPStandardLocalRootLifts.lowerN _ t * KPStandardLocalRootLifts.weylSwap _ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPStandardLocalRootLifts.weylSwap, KPStandardLocalRootLifts.lowerN,
      KubotaRankTwo.n, Matrix.mul_apply, Fin.sum_univ_two]
private theorem sig_right (t : KPHilbert.Completion F (Sum.inr w)) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr w)
      (KPStandardLocalRootLifts.lowerN _ t) (KPStandardLocalRootLifts.weylSwap _) = 1 := by
  let K := KPHilbert.Completion F (Sum.inr w)
  have hX : KubotaRankTwo.X K (KPStandardLocalRootLifts.lowerN K t * KPStandardLocalRootLifts.weylSwap K) = 1 := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.lowerN,
      KPStandardLocalRootLifts.weylSwap, Matrix.mul_apply, Fin.sum_univ_two]
  have hW : KubotaRankTwo.X K (KPStandardLocalRootLifts.weylSwap K) = 1 := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, KPStandardLocalRootLifts.weylSwap]
  have hdet : KubotaRankTwo.det K (KPStandardLocalRootLifts.lowerN K t) = 1 := by
    apply Units.ext
    simp [KPStandardLocalRootLifts.lowerN, Matrix.det_fin_two]
  unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
  rw [hX, hW, hdet]
  simp only [one_mul, div_one]
  rw [KubotaDefectSymbolAlgebra.one_right _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr w)).2.1,
    KubotaDefectSymbolAlgebra.one_left _ _ _ (KPHilbert.B3_laws F ζ hζ (Sum.inr w)).1]
  simp
set_option maxRecDepth 2048 in
private theorem sig_left (t : KPHilbert.Completion F (Sum.inr w)) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr w)
      (KPStandardLocalRootLifts.weylSwap _) (KubotaRankTwo.n _ t) = 1 := by
  have h := KubotaCocycleAlgebra.sigmaTwo_n_mul_mul_n
    (KPHilbert.Completion F (Sum.inr w)) (rootsOfUnity 3 F) (KPHilbert.B3 F ζ hζ (Sum.inr w))
    (KPStandardLocalRootLifts.weylSwap _) 1 0 t
  have hn : KubotaRankTwo.n (KPHilbert.Completion F (Sum.inr w)) 0 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.n]
  rw [hn, one_mul, one_mul] at h
  exact h.trans (KPLocalCover.sigmaTwo_one_right F ζ hζ (Sum.inr w) _)
set_option maxRecDepth 2048 in
private theorem raw_eq (t : KPHilbert.Completion F (Sum.inr w)) :
    KPStandardLocalRootLifts.W F ζ hζ (Sum.inr w) * KPStandardLocalRootLifts.N F ζ hζ (Sum.inr w) t =
    KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inr w) t * KPStandardLocalRootLifts.W F ζ hζ (Sum.inr w) := by
  change KPLocalCover.CubicGL2Raw.mk
      (KPStandardLocalRootLifts.weylSwap _ * KubotaRankTwo.n _ t)
      (1 * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inr w) _ _) =
    KPLocalCover.CubicGL2Raw.mk
      (KPStandardLocalRootLifts.lowerN _ t * KPStandardLocalRootLifts.weylSwap _)
      (1 * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inr w) _ _)
  dsimp only [KPStandardLocalRootLifts.W, KPStandardLocalRootLifts.N,
    KPStandardLocalRootLifts.LowerN, KPLocalCover.sectionMap]
  rw [mat_eq, sig_left, sig_right]

theorem weyl_conjugates_upper (t : KPHilbert.Completion F (Sum.inr w)) :
    KPPGLLocalCover.W F ζ hζ (Sum.inr w) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr w) t *
        (KPPGLLocalCover.W F ζ hζ (Sum.inr w))⁻¹ =
      KPPGLLocalCover.LowerN F ζ hζ (Sum.inr w) t := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  exact congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr w)) (raw_eq F ζ hζ w t) |>.trans (by rw [map_mul]; rfl)

variable (m : ℕ)

theorem coefficient_locally_constant
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothRepresentation ρ) (ℓ : Module.Dual ℂ V)
    (hℓ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothVector ρ.dual ℓ) (v : V) :
    letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
    IsLocallyConstant (coefficient F ζ hζ w ρ ℓ v) := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
  letI : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  obtain ⟨J, hJ⟩ := hρ v
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (J : Set _),
    J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro x hx
    have heq : x = g * (g⁻¹ * x) := by simp
    rw [coefficient, heq, map_mul, Module.End.mul_apply, hJ _ hx]
    rfl

private theorem single_tail
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hJ : Subsingleton (UpperJacquet F ζ hζ w ρ))
    (ℓ : Module.Dual ℂ V) (hℓ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothVector ρ.dual ℓ) (v : V) :
    ∀ᶠ n : ℕ in atTop, coefficient F ζ hζ w ρ ℓ v (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) = 0 := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
  obtain ⟨J, hfix⟩ := hℓ
  have hlinear (x : V) : x ∈ rootRelationSpan ρ (upperRoot F ζ hζ w) 1 := by
    rw [← rootCoinvariantsMk_ker, LinearMap.mem_ker]
    exact @Subsingleton.elim _ hJ _ _
  induction hlinear v using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨t, u⟩, rfl⟩ := hx
    have ht : Tendsto (fun n : ℕ => (π : w.adicCompletion F) ^ n * t.toAdd) atTop (𝓝 0) := by
      simpa using (Valued.tendsto_zero_pow_of_le_exp_neg_one hπ.le).mul_const t.toAdd
    have hN0 : KPPGLLocalCover.N F ζ hζ (Sum.inr w) 0 = 1 := by
      simp [KPPGLLocalCover.N]
    have hN := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1.tendsto 0 |>.comp ht
    rw [hN0] at hN
    have hev := hN.eventually (J.isOpen.mem_nhds J.one_mem)
    filter_upwards [hev] with n hn
    have hdual := congrArg (fun f : Module.Dual ℂ V => f (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) u))
      (hfix _ (J.inv_mem hn))
    simp only [Representation.dual_apply, Module.Dual.transpose_apply, inv_inv] at hdual
    change ℓ (ρ (KPPGLLocalCover.N F ζ hζ (Sum.inr w) ((π : w.adicCompletion F) ^ n * t.toAdd))
      (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) u)) = _ at hdual
    have hcomm : KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n * upperRoot F ζ hζ w t =
      KPPGLLocalCover.N F ζ hζ (Sum.inr w) ((π : w.adicCompletion F) ^ n * t.toAdd) *
      KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n := by
      symm
      simpa [KPRankOneCartanGeometry.diagonalLift, upperRoot, KPStandardLocalRootLifts.N_hom,
        KPPGLLocalCover.N, mul_div_cancel_left₀ _ (pow_ne_zero n π.ne_zero)] using
        KPCorrectedBruhatLifts.quotient_upper_diagonal F ζ hζ (Sum.inr w)
          ((π : w.adicCompletion F) ^ n * t.toAdd) (π ^ n)
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, coefficient]
    rw [map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    exact sub_eq_zero.mpr hdual
  | zero => simp [coefficient]
  | add x y hx hy ihx ihy =>
    filter_upwards [ihx, ihy] with n hn hn'
    change ℓ (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) (x + y)) = 0
    change ℓ (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) x) = 0 at hn
    change ℓ (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) y) = 0 at hn'
    rw [map_add, map_add, hn, hn', add_zero]
  | smul c x hx ih =>
    filter_upwards [ih] with n hn
    change ℓ (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) (c • x)) = 0
    change ℓ (ρ (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) x) = 0 at hn
    rw [map_smul, map_smul, hn, smul_zero]
private theorem orbit_lc {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G X) (x : X)
    (hx : SmoothVector σ x) : IsLocallyConstant (fun g => σ g x) := by
  obtain ⟨J, hJ⟩ := hx
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun y => g⁻¹ * y) ⁻¹' (J : Set _),
    J.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using J.one_mem
  · intro y hy
    have heq : y = g * (g⁻¹ * y) := by simp
    rw [heq, map_mul, Module.End.mul_apply, hJ _ hy]
private theorem smooth_translate {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G X) (x : X)
    (hx : SmoothVector σ x) (g : G) : SmoothVector σ (σ g x) := by
  obtain ⟨J, hJ⟩ := hx
  refine ⟨J.comap (MulAut.conj g⁻¹).toMonoidHom ?_, ?_⟩
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · intro j hj
    have heq : j * g = g * (g⁻¹ * j * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, Module.End.mul_apply]
    have hj' : g⁻¹ * j * g ∈ J := by simpa [MulAut.conj_apply] using hj
    exact congrArg (σ g) (hJ _ hj')

theorem coefficient_covered_cartan_tail_zero
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hρ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothRepresentation ρ)
    (hJ : Subsingleton (UpperJacquet F ζ hζ w ρ))
    (ℓ : Module.Dual ℂ V) (hℓ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothVector ρ.dual ℓ) (v : V) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
      ∀ k₁ k₂ : KPRankOneCartanGeometry.coveredK0 F ζ hζ w,
        coefficient F ζ hζ w ρ ℓ v
          (k₁.val * KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n * k₂.val) = 0 := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
  letI : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr w)) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  letI : CompactSpace (KPRankOneCartanGeometry.coveredK0 F ζ hζ w) :=
    isCompact_iff_compactSpace.mp (KPRankOneCartanGeometry.coveredK0_compact_open F ζ hζ w m hm).1
  let r := fun k : KPRankOneCartanGeometry.coveredK0 F ζ hζ w => ρ k.val v
  let l := fun k : KPRankOneCartanGeometry.coveredK0 F ζ hζ w => ρ.dual k.val⁻¹ ℓ
  have hr : (Set.range r).Finite := ((orbit_lc ρ v (hρ v)).comp_continuous continuous_subtype_val).range_finite
  have hl : (Set.range l).Finite := ((orbit_lc ρ.dual ℓ hℓ).comp_continuous continuous_subtype_val.inv).range_finite
  have hev : ∀ᶠ n : ℕ in atTop, ∀ a ∈ Set.range l, ∀ b ∈ Set.range r,
      coefficient F ζ hζ w ρ a b (KPRankOneCartanGeometry.diagonalLift F ζ hζ w π n) = 0 := by
    rw [Filter.eventually_all_finite hl]
    intro a ha
    rw [Filter.eventually_all_finite hr]
    intro b hb
    obtain ⟨k, rfl⟩ := ha
    exact single_tail F ζ hζ w ρ m hm π hπ hJ _ (smooth_translate ρ.dual ℓ hℓ k.val⁻¹) b
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  refine ⟨M, ?_⟩
  intro n hn k₁ k₂
  have h := hM n hn (l k₁) (Set.mem_range_self k₁) (r k₂) (Set.mem_range_self k₂)
  simpa [l, r, coefficient, Representation.dual_apply, Module.Dual.transpose_apply,
    map_mul, Module.End.mul_apply] using h

theorem coefficient_support_in_cartan_truncation
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (π : (w.adicCompletion F)ˣ)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (hρ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothRepresentation ρ)
    (hJ : Subsingleton (UpperJacquet F ζ hζ w ρ))
    (ℓ : Module.Dual ℂ V) (hℓ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothVector ρ.dual ℓ) (v : V) :
    ∃ M : ℕ, Function.support (coefficient F ζ hζ w ρ ℓ v) ⊆
      KPRankOneCartanGeometry.cartanTruncation F ζ hζ w π M := by
  obtain ⟨M, hM⟩ := coefficient_covered_cartan_tail_zero F ζ hζ w ρ m hm π hπ hρ hJ ℓ hℓ v
  refine ⟨M, ?_⟩
  intro g hg
  obtain ⟨n, k₁, k₂, rfl⟩ := KPRankOneCartanGeometry.cartan_decomposition F ζ hζ w π hπ g
  have hn : n ≤ M := by
    by_contra hn
    exact hg (hM n (by omega) k₁ k₂)
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, ⟨k₁, k₂, rfl⟩⟩⟩

theorem coefficient_compact_support
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hρ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothRepresentation ρ)
    (hJ : Subsingleton (UpperJacquet F ζ hζ w ρ))
    (ℓ : Module.Dual ℂ V) (hℓ : letI := KPPGLLocalCover.finiteTopology F ζ hζ w m;
      SmoothVector ρ.dual ℓ) (v : V) :
    letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
    IsCompact (Function.support (coefficient F ζ hζ w ρ ℓ v)) ∧
      HasCompactSupport (coefficient F ζ hζ w ρ ℓ v) := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ w m
  obtain ⟨p, hp⟩ := w.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    intro h
    have he := hp
    rw [h, map_zero] at he
    exact WithZero.exp_ne_zero he.symm
  let π : (w.adicCompletion F)ˣ := Units.mk0 p hp0
  obtain ⟨M, hM⟩ := coefficient_support_in_cartan_truncation F ζ hζ w ρ m hm π hp hρ hJ ℓ hℓ v
  have hc := coefficient_locally_constant F ζ hζ w ρ m hm hρ ℓ hℓ v
  have hs : IsClosed (Function.support (coefficient F ζ hζ w ρ ℓ v)) := by
    change IsClosed ({x | coefficient F ζ hζ w ρ ℓ v x = 0}ᶜ)
    exact (hc.isOpen_fiber 0).isClosed_compl
  have hcompact := (KPRankOneCartanGeometry.cartanTruncation_compact F ζ hζ w m hm π M).of_isClosed_subset hs hM
  refine ⟨hcompact, ?_⟩
  simpa [HasCompactSupport, tsupport, hs.closure_eq] using hcompact

end
end DedekindZetaZeroFree.KPRankOneJacquetZeroCompactCoefficients
