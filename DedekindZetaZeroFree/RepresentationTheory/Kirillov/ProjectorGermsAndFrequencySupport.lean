module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.InductionReciprocity
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.FiniteBallFourierProjectors

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPKirillovProjectorGerms

open scoped NumberField Classical
open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (𝓞 F))

def frequencyCharacter (t : w.adicCompletion F) :
    Multiplicative (w.adicCompletion F) →* ℂˣ where
  toFun x := Circle.toUnits (localFiniteCharacter F w (t * Multiplicative.toAdd x))
  map_one' := by simp
  map_mul' x y := by
    change Circle.toUnits (localFiniteCharacter F w
        (t * (Multiplicative.toAdd x + Multiplicative.toAdd y))) =
      Circle.toUnits (localFiniteCharacter F w (t * Multiplicative.toAdd x)) *
        Circle.toUnits (localFiniteCharacter F w (t * Multiplicative.toAdd y))
    rw [mul_add, AddChar.map_add_eq_mul, map_mul]

@[simp] theorem frequencyCharacter_apply (t x : w.adicCompletion F) :
    (frequencyCharacter F w t (Multiplicative.ofAdd x) : ℂ) =
      (localFiniteCharacter F w (t * x) : ℂ) := rfl

@[simp] theorem frequencyCharacter_zero : frequencyCharacter F w 0 = 1 := by
  ext x
  simp [frequencyCharacter]

end DedekindZetaZeroFree.KPKirillovProjectorGerms

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPKirillovProjectorGerms

open scoped NumberField Classical
open NumberField IsDedekindDomain
open KPKirillovFiniteBallProjectors

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (𝓞 F))

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V)

abbrev Fiber (t : w.adicCompletion F) :=
  KPLocalSmoothRepresentation.TwistedCoinvariants F ζ hζ w ρ
    (frequencyCharacter F w t)

def quotientMap (t : w.adicCompletion F) : V →ₗ[ℂ] Fiber F ζ hζ w ρ t :=
  rootCoinvariantsMk ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w)
    (frequencyCharacter F w t)

def ordinaryQuotientMap :
    V →ₗ[ℂ] KPLocalSmoothRepresentation.OrdinaryCoinvariants F ζ hζ w ρ :=
  rootCoinvariantsMk ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) 1

def ordinaryKernel : Submodule ℂ V :=
  LinearMap.ker (quotientMap F ζ hζ w ρ 0)

theorem ordinaryKernel_eq_ker_ordinaryQuotientMap :
    ordinaryKernel F ζ hζ w ρ =
      LinearMap.ker (ordinaryQuotientMap F ζ hζ w ρ) := by
  exact congrArg (fun ψ => LinearMap.ker (rootCoinvariantsMk ρ
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) ψ)) (frequencyCharacter_zero F w)

theorem ordinaryKernel_eq_span :
    ordinaryKernel F ζ hζ w ρ =
      Submodule.span ℂ (Set.range fun xv : w.adicCompletion F × V =>
        rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd xv.1) xv.2 - xv.2) := by
  rw [ordinaryKernel_eq_ker_ordinaryQuotientMap, ordinaryQuotientMap, rootCoinvariantsMk_ker]
  unfold rootRelationSpan
  congr 1
  apply Set.ext
  intro v
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(Multiplicative.toAdd x, y), by simp [rootRepresentation]⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(Multiplicative.ofAdd x, y), by simp [rootRepresentation]⟩

theorem quotientMap_zero_eq_zero_iff (v : V) :
    quotientMap F ζ hζ w ρ 0 v = 0 ↔ v ∈ ordinaryKernel F ζ hζ w ρ := by
  rfl

theorem ordinaryKernel_borel_stable
    (p : KPLocalSmoothRepresentation.Borel F ζ hζ w) (v : V)
    (hv : v ∈ ordinaryKernel F ζ hζ w ρ) :
    ρ p.val v ∈ ordinaryKernel F ζ hζ w ρ := by
  rw [ordinaryKernel_eq_span] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨x, v⟩, rfl⟩ := hz
    let nb : KPLocalSmoothRepresentation.Borel F ζ hζ w :=
      ⟨KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd x),
        KPLocalInductionJacquetReciprocity.upperRoot_mem_borel F ζ hζ w _⟩
    have hk : KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
        (p * nb * p⁻¹) = 1 := by
      simp [nb]
    obtain ⟨y, hy⟩ := (KPLocalInductionJacquetReciprocity.borelRetraction_kernel
      F ζ hζ w (p * nb * p⁻¹)).mp hk
    change p.val * KPLocalSmoothRepresentation.upperRoot F ζ hζ w
      (Multiplicative.ofAdd x) * p.val⁻¹ =
        KPLocalSmoothRepresentation.upperRoot F ζ hζ w y at hy
    have heq : p.val * KPLocalSmoothRepresentation.upperRoot F ζ hζ w
        (Multiplicative.ofAdd x) =
        KPLocalSmoothRepresentation.upperRoot F ζ hζ w y * p.val := by
      rw [← hy]; group
    have he : ρ p.val (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) =
        rootRepresentation F ζ hζ w ρ y (ρ p.val v) := by
      change ρ p.val (ρ _ v) = ρ _ (ρ p.val v)
      rw [← Module.End.mul_apply, ← ρ.map_mul, heq, ρ.map_mul, Module.End.mul_apply]
    rw [map_sub, he]
    apply Submodule.subset_span
    exact ⟨(Multiplicative.toAdd y, ρ p.val v), rfl⟩
  | zero => simpa using (Submodule.zero_mem _)
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (hρ : IsSmooth F ζ hζ w m ρ)

theorem quotientMap_projector (u : ℤ) (t : w.adicCompletion F) (v : V) :
    quotientMap F ζ hζ w ρ t (projector F ζ hζ w ρ m hm hρ u t v) =
      quotientMap F ζ hζ w ρ t v := by
  let l := averagingDepth F ζ hζ w ρ m hm hρ u t v
  have hl := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
  letI := finite_finiteCompletionBallQuotient F w u l hl.1
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  have hterm (x : w.adicCompletion F) :
      quotientMap F ζ hζ w ρ t
          ((localFiniteCharacter F w (-t * x) : ℂ) •
            rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) =
        quotientMap F ζ hζ w ρ t v := by
    rw [map_smul]
    change _ • rootCoinvariantsMk ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w)
      (frequencyCharacter F w t) (ρ _ v) = _
    rw [rootCoinvariantsMk_equivariant]
    simp only [frequencyCharacter_apply, ← neg_mul, smul_smul]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    simp [neg_mul, quotientMap]
  change quotientMap F ζ hζ w ρ t
    (levelAverage F ζ hζ w ρ u l hl.1 t v) = _
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum]
  change (Nat.card (finiteCompletionBallQuotient F w u l) : ℂ)⁻¹ •
    ∑ q : finiteCompletionBallQuotient F w u l,
      quotientMap F ζ hζ w ρ t ((localFiniteCharacter F w
        (-t * ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F)) : ℂ) •
        rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd
          ((Quotient.out q : finiteCompletionBall F w u) : w.adicCompletion F)) v) = _
  simp only [hterm, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp [Nat.card_eq_fintype_card]

private theorem projector_root_commutes (u : ℤ) (t x : w.adicCompletion F) (v : V) :
    projector F ζ hζ w ρ m hm hρ u t
        (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) =
      rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x)
        (projector F ζ hζ w ρ m hm hρ u t v) := by
  let l := averagingDepth F ζ hζ w ρ m hm hρ u t v
  have hl := averagingDepth_spec F ζ hζ w ρ m hm hρ u t v
  have hc (y : w.adicCompletion F) :
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd y))
        (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) =
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x))
        (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd y) v) := by
    change ((rootRepresentation F ζ hζ w ρ _ * rootRepresentation F ζ hζ w ρ _) v) =
      ((rootRepresentation F ζ hζ w ρ _ * rootRepresentation F ζ hζ w ρ _) v)
    rw [← (rootRepresentation F ζ hζ w ρ).map_mul,
      ← (rootRepresentation F ζ hζ w ρ).map_mul, mul_comm]
  have hfix : FixedByBall F ζ hζ w ρ l
      (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd x) v) := by
    intro y hy
    rw [hc, hl.2.1 y hy]
  simp only [projector_apply]
  rw [projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u l hl.1 t hl.2.2 _ hfix,
    projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u l hl.1 t hl.2.2 v hl.2.1]
  letI := finite_finiteCompletionBallQuotient F w u l hl.1
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u l)
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, hc]

private theorem projector_commutes (u u' : ℤ) (t : w.adicCompletion F) :
    Commute (projector F ζ hζ w ρ m hm hρ u t)
      (projector F ζ hζ w ρ m hm hρ u' t) := by
  apply LinearMap.ext
  intro v
  let l := averagingDepth F ζ hζ w ρ m hm hρ u' t v
  have hl := averagingDepth_spec F ζ hζ w ρ m hm hρ u' t v
  have hfix : FixedByBall F ζ hζ w ρ l
      (projector F ζ hζ w ρ m hm hρ u t v) := by
    intro x hx
    rw [← projector_root_commutes, hl.2.1 x hx]
  change projector F ζ hζ w ρ m hm hρ u t
    (projectorValue F ζ hζ w ρ m hm hρ u' t v) =
      projectorValue F ζ hζ w ρ m hm hρ u' t
        (projector F ζ hζ w ρ m hm hρ u t v)
  rw [projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u' l hl.1 t hl.2.2 v hl.2.1,
    projectorValue_eq_levelAverage F ζ hζ w ρ m hm hρ u' l hl.1 t hl.2.2 _ hfix]
  letI := finite_finiteCompletionBallQuotient F w u' l hl.1
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F w u' l)
  simp only [levelAverage, levelAverageWithRepresentatives, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, projector_root_commutes]

theorem quotientMap_eq_zero_iff_exists_projector_eq_zero
    (t : w.adicCompletion F) (v : V) :
    quotientMap F ζ hζ w ρ t v = 0 ↔
      ∃ u : ℤ, projector F ζ hζ w ρ m hm hρ u t v = 0 := by
  have href (u u' : ℤ) (h : u' ≤ u) (v : V)
      (hv : projector F ζ hζ w ρ m hm hρ u t v = 0) :
      projector F ζ hζ w ρ m hm hρ u' t v = 0 := by
    have he := projector_refinement_eq F ζ hζ w ρ m hm hρ u u' h t t (by simp)
    have hc := projector_commutes F ζ hζ w ρ m hm hρ u u' t
    have he' := LinearMap.congr_fun (hc.symm.eq.trans he) v
    change projector F ζ hζ w ρ m hm hρ u' t
      (projector F ζ hζ w ρ m hm hρ u t v) =
        projector F ζ hζ w ρ m hm hρ u' t v at he'
    rw [hv, map_zero] at he'
    exact he'.symm
  constructor
  · intro hv
    have hmem : v ∈ rootRelationSpan ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ w)
        (frequencyCharacter F w t) := by
      rw [← rootCoinvariantsMk_ker]
      exact hv
    clear hv
    induction hmem using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, v⟩, rfl⟩ := hz
      have hxall : Multiplicative.toAdd x ∈
          ⋃ n : ℕ, (finiteCompletionBall F w (-(n : ℤ)) : Set (w.adicCompletion F)) := by
        rw [iUnion_finiteCompletionBall_neg_nat]
        trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxall
      refine ⟨-(n : ℤ), ?_⟩
      rw [map_sub, map_smul]
      change projector F ζ hζ w ρ m hm hρ (-(n : ℤ)) t
        (rootRepresentation F ζ hζ w ρ (Multiplicative.ofAdd (Multiplicative.toAdd x)) v) - _ = 0
      rw [projector_root_commutes, projector_eigen F ζ hζ w ρ m hm hρ _ _ _ hn]
      change _ • _ - (frequencyCharacter F w t (Multiplicative.ofAdd (Multiplicative.toAdd x)) : ℂ) • _ = 0
      rw [frequencyCharacter_apply, sub_self]
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨u', hu'⟩ := ihy
      refine ⟨min u u', ?_⟩
      rw [map_add, href u _ (min_le_left _ _) x hu, href u' _ (min_le_right _ _) y hu']
      simp
    | smul c x hx ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, by rw [map_smul, hu, smul_zero]⟩
  · rintro ⟨u, hu⟩
    rw [← quotientMap_projector F ζ hζ w ρ m hm hρ u t v, hu, map_zero]

include hm hρ in

theorem eq_zero_of_all_quotientMap_eq_zero (v : V)
    (hv : ∀ t : w.adicCompletion F, quotientMap F ζ hζ w ρ t v = 0) :
    v = 0 := by
  obtain ⟨l, _, hl, _⟩ := exists_averagingDepth F ζ hζ w ρ m hm hρ 0 0 v
  let depth : w.adicCompletion F → ℤ := fun t =>
    Classical.choose ((quotientMap_eq_zero_iff_exists_projector_eq_zero
      F ζ hζ w ρ m hm hρ t v).mp (hv t))
  have hz (t : w.adicCompletion F) :
      projector F ζ hζ w ρ m hm hρ (depth t) t v = 0 :=
    Classical.choose_spec ((quotientMap_eq_zero_iff_exists_projector_eq_zero
      F ζ hζ w ρ m hm hρ t v).mp (hv t))
  let O : w.adicCompletion F → Set (w.adicCompletion F) := fun t =>
    {s | s - t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w (depth t))}
  have hopen (t : w.adicCompletion F) : IsOpen (O t) := by
    simpa only [O, localFiniteAnnihilator_finiteCompletionBall] using
      isOpen_finiteCompletionBall_coset F w t (-depth t - localDifferentExponent F w)
  have hcompact : IsCompact (localFiniteAnnihilator F w (finiteCompletionBall F w l) :
      Set (w.adicCompletion F)) := by
    rw [localFiniteAnnihilator_finiteCompletionBall]
    exact isCompact_finiteCompletionBall F w _
  obtain ⟨S, hS⟩ := hcompact.elim_finite_subcover O hopen (by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨t, by simp [O]⟩)
  obtain ⟨u, hu⟩ := (S.image depth : Finset (OrderDual ℤ)).exists_le
  let u' : ℤ := min u l
  have hall (t : w.adicCompletion F)
      (ht : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w l)) :
      projector F ζ hζ w ρ m hm hρ u' t v = 0 := by
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (hS ht)
    obtain ⟨hsS, hts⟩ := Set.mem_iUnion.mp hs
    have hsmall : u' ≤ depth s := le_trans (min_le_left _ _) (hu _ (Finset.mem_image.mpr ⟨s, hsS, rfl⟩))
    have hzero : projector F ζ hζ w ρ m hm hρ (depth s) t v = 0 := by
      rw [projector_eq_of_sub_mem_annihilator F ζ hζ w ρ m hm hρ _ t s hts, hz]
    have he := projector_refinement_eq F ζ hζ w ρ m hm hρ (depth s) u' hsmall t t (by simp)
    have hc := projector_commutes F ζ hζ w ρ m hm hρ (depth s) u' t
    have he' := LinearMap.congr_fun (hc.symm.eq.trans he) v
    change projector F ζ hζ w ρ m hm hρ u' t
      (projector F ζ hζ w ρ m hm hρ (depth s) t v) =
        projector F ζ hζ w ρ m hm hρ u' t v at he'
    rw [hzero, map_zero] at he'
    exact he'.symm
  letI := finite_dualQuotient F w u' l (min_le_right _ _)
  letI := Fintype.ofFinite (DualQuotient F w u' l)
  rw [finite_fourier_decomposition F ζ hζ w ρ m hm hρ u' l (min_le_right _ _) v hl]
  apply Finset.sum_eq_zero
  intro q hq
  exact hall _ (Quotient.out q).property

def characterProjectorSupport (v : V) : Set (w.adicCompletion F) :=
  {t | ∀ u : ℤ, projector F ζ hζ w ρ m hm hρ u t v ≠ 0}

theorem mem_characterProjectorSupport_iff (t : w.adicCompletion F) (v : V) :
    t ∈ characterProjectorSupport F ζ hζ w ρ m hm hρ v ↔
      quotientMap F ζ hζ w ρ t v ≠ 0 := by
  simpa only [not_exists, characterProjectorSupport, Set.mem_setOf_eq] using
    (not_congr (quotientMap_eq_zero_iff_exists_projector_eq_zero
      F ζ hζ w ρ m hm hρ t v)).symm

theorem characterProjectorSupport_subset_annihilator (l : ℤ) (v : V)
    (hv : FixedByBall F ζ hζ w ρ l v) :
    characterProjectorSupport F ζ hζ w ρ m hm hρ v ⊆
      (localFiniteAnnihilator F w (finiteCompletionBall F w l) :
        Set (w.adicCompletion F)) := by
  intro t ht
  by_contra hnot
  have hfix : projector F ζ hζ w ρ m hm hρ l 0 v = v :=
    projector_eq_self F ζ hζ w ρ m hm hρ l 0 v (by
      intro x hx
      simpa using hv x hx)
  have hz := projector_orthogonal F ζ hζ w ρ m hm hρ l t 0 (by simpa using hnot)
  have hzv := LinearMap.congr_fun hz v
  simp only [LinearMap.comp_apply, hfix, LinearMap.zero_apply] at hzv
  exact ht l hzv

theorem exists_stabilizing_ball_support_bound (v : V) :
    ∃ l : ℤ, FixedByBall F ζ hζ w ρ l v ∧
      characterProjectorSupport F ζ hζ w ρ m hm hρ v ⊆
        (localFiniteAnnihilator F w (finiteCompletionBall F w l) :
          Set (w.adicCompletion F)) := by
  obtain ⟨l, _, hl, _⟩ := exists_averagingDepth F ζ hζ w ρ m hm hρ 0 0 v
  exact ⟨l, hl, characterProjectorSupport_subset_annihilator F ζ hζ w ρ m hm hρ l v hl⟩

theorem ordinaryKernel_support_compact_away_zero (v : V)
    (hv : v ∈ ordinaryKernel F ζ hζ w ρ) :
    ∃ C : Set (w.adicCompletion F)ˣ, IsCompact C ∧
      characterProjectorSupport F ζ hζ w ρ m hm hρ v ⊆
        (fun a : (w.adicCompletion F)ˣ => (a : w.adicCompletion F)) '' C := by
  obtain ⟨l, hl, hs⟩ := exists_stabilizing_ball_support_bound F ζ hζ w ρ m hm hρ v
  obtain ⟨u, hu⟩ := (quotientMap_eq_zero_iff_exists_projector_eq_zero
    F ζ hζ w ρ m hm hρ 0 v).mp hv
  let A := localFiniteAnnihilator F w (finiteCompletionBall F w l)
  let B := localFiniteAnnihilator F w (finiteCompletionBall F w u)
  let D : Set (w.adicCompletion F) := (A : Set (w.adicCompletion F)) \ (B : Set (w.adicCompletion F))
  have hD : IsCompact D := by
    apply IsCompact.diff
    · change IsCompact (localFiniteAnnihilator F w (finiteCompletionBall F w l) : Set (w.adicCompletion F))
      rw [localFiniteAnnihilator_finiteCompletionBall]
      exact isCompact_finiteCompletionBall F w _
    · change IsOpen (localFiniteAnnihilator F w (finiteCompletionBall F w u) : Set (w.adicCompletion F))
      rw [localFiniteAnnihilator_finiteCompletionBall]
      exact isOpen_finiteCompletionBall F w _
  have haway : ∀ t ∈ D, t ≠ 0 := by
    intro t ht he
    exact ht.2 (he ▸ B.zero_mem)
  let lift : D → (w.adicCompletion F)ˣ := fun t => Units.mk0 t.val (haway t.val t.property)
  have hcont : Continuous lift := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · exact continuous_subtype_val.inv₀ (fun t => haway t.val t.property)
  refine ⟨Set.range lift, ?_, ?_⟩
  · letI := isCompact_iff_compactSpace.mp hD
    exact isCompact_range hcont
  · intro t ht
    have htD : t ∈ D := by
      refine ⟨hs ht, ?_⟩
      intro htB
      have htB' : t ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u) := htB
      have he := projector_eq_of_sub_mem_annihilator F ζ hζ w ρ m hm hρ u t 0 (by rw [sub_zero]; exact htB')
      exact ht u (by rw [he, hu])
    refine ⟨lift ⟨t, htD⟩, Set.mem_range_self _, rfl⟩

end DedekindZetaZeroFree.KPKirillovProjectorGerms

end
end
