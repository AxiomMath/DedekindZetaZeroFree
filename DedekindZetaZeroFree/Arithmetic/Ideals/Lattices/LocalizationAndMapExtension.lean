module

public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.FullLatticesAndRationalLines

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

theorem kp_cusp_full_lattice_clear_denominators
    (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (V : Type*) [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] [FiniteDimensional K V]
    (M : Submodule R V) [Submodule.IsLattice K M] (x : V) :
    ∃ r : R, r ≠ 0 ∧ (algebraMap R K r) • x ∈ M := by
  have clear (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
      ∃ r : R, r ≠ 0 ∧ (algebraMap R K r) • x ∈ M := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [map_mul, smul_add]
      have hx' : (algebraMap R K (a * b)) • x ∈ M := by
        simpa only [map_mul, algebraMap_smul, mul_smul, smul_comm a b] using M.smul_mem b hxa
      have hy' : (algebraMap R K (a * b)) • y ∈ M := by
        simpa only [map_mul, ← smul_smul, algebraMap_smul] using M.smul_mem a hyb
      exact M.add_mem (by simpa only [map_mul] using hx') (by simpa only [map_mul] using hy')
    | smul c x _ hx =>
      obtain ⟨r, hr, hxr⟩ := hx
      obtain ⟨a, b, hb, hc⟩ := IsFractionRing.div_surjective R c
      have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
      refine ⟨b * r, mul_ne_zero hb' hr, ?_⟩
      have hbK : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb'
      have hs : (algebraMap R K (b * r)) * c =
          algebraMap R K (a * r) := by
        rw [map_mul, map_mul, ← hc]
        field_simp
      rw [smul_smul, hs, map_mul, mul_smul, algebraMap_smul]
      exact M.smul_mem a hxr
  apply clear
  rw [Submodule.IsLattice.span_eq_top]
  trivial

private theorem localizedSubmodule
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V)
    (h : ∀ x : V, ∃ r : R, r ≠ 0 ∧ (algebraMap R K r) • x ∈ M) :
    IsLocalizedModule R⁰ M.subtype where
  map_units s := (isLocalizedModule_id R⁰ V K).map_units s
  surj x := by
    obtain ⟨r, hr, hx⟩ := h x
    exact ⟨(⟨(algebraMap R K r) • x, hx⟩, ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩),
      by simp only [Submonoid.smul_def, Submodule.subtype_apply, algebraMap_smul]⟩
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

theorem kp_cusp_full_lattice_equiv_extension
    (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (V W : Type*) [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module K V] [IsScalarTower R K V]
    [Module R W] [Module K W] [IsScalarTower R K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : Submodule R V) (N : Submodule R W)
    [Submodule.IsLattice K M] [Submodule.IsLattice K N]
    (f : M ≃ₗ[R] N) :
    ∃! fK : V ≃ₗ[K] W,
      (∀ m : M, fK (m : V) = (f m : W)) ∧
      Submodule.map (fK.toLinearMap.restrictScalars R) M = N := by
  letI := localizedSubmodule M (kp_cusp_full_lattice_clear_denominators R K V M)
  letI := localizedSubmodule N (kp_cusp_full_lattice_clear_denominators R K W N)
  let F := IsLocalizedModule.mapEquiv R⁰ M.subtype N.subtype K f
  have hF : ∀ m : M, F (m : V) = (f m : W) := by
    intro m
    exact IsLocalizedModule.map_apply R⁰ M.subtype N.subtype f.toLinearMap m
  refine ⟨F, ⟨hF, ?_⟩, ?_⟩
  · ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change F v ∈ N
      rw [hF ⟨v, hv⟩]
      exact (f ⟨v, hv⟩).property
    · intro hw
      refine ⟨(f.symm ⟨w, hw⟩ : V), (f.symm ⟨w, hw⟩).property, ?_⟩
      change F (f.symm ⟨w, hw⟩ : V) = w
      rw [hF]
      simp
  · intro G hG
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext R⁰ M.subtype N.subtype
    ext m
    exact (hG.1 m).trans (hF m).symm

private theorem fractionalIdealNonzero
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t : K, t ∈ I ∧ t ≠ 0 := by
  by_contra h
  apply hI
  apply (FractionalIdeal.eq_zero_iff).2
  intro t ht
  by_contra ht0
  exact h ⟨t, ht, ht0⟩

private theorem fractionalIdealClear
    {R : Type*} [CommRing R] [IsDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : K) :
    ∃ r : R, r ≠ 0 ∧ (algebraMap R K r) • x ∈ I := by
  obtain ⟨t, ht, ht0⟩ := fractionalIdealNonzero I hI
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective R (x / t)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb0
  refine ⟨b, hb0, ?_⟩
  have hbt : (algebraMap R K b) * x = (algebraMap R K a) * t := by
    have := (div_eq_div_iff hbK ht0).mp heq
    simpa only [mul_comm] using this.symm
  rw [smul_eq_mul, hbt, ← smul_eq_mul, algebraMap_smul]
  exact I.1.smul_mem a ht

theorem kp_cusp_fractional_ideal_map_scalar
    (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (f : I →ₗ[R] K) :
    ∃! c : K, ∀ t : I, f t = c * (t : K) := by
  letI := localizedSubmodule (I : Submodule R K) (fractionalIdealClear I hI)
  letI := isLocalizedModule_id R⁰ K K
  let F : K →ₗ[K] K := IsLocalizedModule.mapExtendScalars R⁰
    (I : Submodule R K).subtype (LinearMap.id : K →ₗ[R] K) K f
  have hF (t : I) : F (t : K) = f t :=
    IsLocalizedModule.map_apply R⁰ (I : Submodule R K).subtype
      (LinearMap.id : K →ₗ[R] K) f t
  have scalar (x : K) : F x = F 1 * x := by
    have := F.map_smul x (1 : K)
    simpa only [smul_eq_mul, mul_one, mul_comm] using this
  refine ⟨F 1, fun t => by rw [← hF, scalar], ?_⟩
  intro c hc
  obtain ⟨t, ht, ht0⟩ := fractionalIdealNonzero I hI
  apply mul_right_cancel₀ ht0
  rw [← scalar, hF ⟨t, ht⟩, hc ⟨t, ht⟩]

theorem kp_cusp_fractional_ideal_equiv_iff
    (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) :
    Nonempty (I ≃ₗ[R] J) ↔
      ∃ c : K, c ≠ 0 ∧ FractionalIdeal.spanSingleton R⁰ c * I = J := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨c, hc, _⟩ := kp_cusp_fractional_ideal_map_scalar R K I hI
      ((J : Submodule R K).subtype.comp f.toLinearMap)
    have hcf (t : I) : (f t : K) = c * (t : K) := hc t
    have hc0 : c ≠ 0 := by
      intro hc0
      obtain ⟨t, ht, ht0⟩ := fractionalIdealNonzero I hI
      have hf0 : f ⟨t, ht⟩ = 0 := by
        apply Subtype.ext
        simpa [hc0] using hcf ⟨t, ht⟩
      have : (⟨t, ht⟩ : (I : Submodule R K)) = 0 := f.injective (by simpa only [map_zero] using hf0)
      exact ht0 (congrArg Subtype.val this)
    refine ⟨c, hc0, ?_⟩
    ext x
    rw [FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [← hcf ⟨t, ht⟩]
      exact (f ⟨t, ht⟩).property
    · intro hx
      refine ⟨(f.symm ⟨x, hx⟩ : K), (f.symm ⟨x, hx⟩).property, ?_⟩
      rw [← hcf]
      simp
  · rintro ⟨c, hc0, hc⟩
    let g : I →ₗ[R] J :=
      { toFun := fun t => ⟨c * (t : K), by
          rw [← hc]
          exact FractionalIdeal.mem_singleton_mul.mpr ⟨t, t.property, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (by simp [mul_add])
        map_smul' := fun r x => Subtype.ext (by
          simp only [Submodule.coe_smul, Algebra.smul_def, RingHom.id_apply]
          ring) }
    refine ⟨LinearEquiv.ofBijective g ⟨?_, ?_⟩⟩
    · intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ hc0 (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : K) ∈ FractionalIdeal.spanSingleton R⁰ c * I := by
        rw [hc]
        exact y.property
      obtain ⟨t, ht, heq⟩ := FractionalIdeal.mem_singleton_mul.mp hy
      exact ⟨⟨t, ht⟩, Subtype.ext heq.symm⟩

end DedekindZetaZeroFree
