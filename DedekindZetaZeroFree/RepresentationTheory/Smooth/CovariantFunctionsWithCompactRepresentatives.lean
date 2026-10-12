module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCompactHolomorphicModel

@[expose] public section

open scoped Topology
namespace DedekindZetaZeroFree.KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps
open KPLocalPrincipalSeries
noncomputable section
set_option autoImplicit false

theorem covariant_smooth_of_compact_representatives
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]
    (B : Subgroup G) (ρ : Representation ℂ B V) (f : G → V)
    (hcov : ∀ (b : B) (g : G), f ((b : G) * g) = ρ b (f g))
    (hlc : IsLocallyConstant f)
    (C : Set G) (hC : IsCompact C)
    (hrep : ∀ g : G, f g ≠ 0 →
      ∃ (b : B) (c : G), c ∈ C ∧ g = (b : G) * c) :
    SmoothVector vectorRightTranslation f := by

  have hA : IsOpen {p : G × G | f p.1 = f p.2} := by
    have heq : {p : G × G | f p.1 = f p.2}
        = ⋃ v : V, (f ⁻¹' {v}) ×ˢ (f ⁻¹' {v}) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨f p.1, rfl, h.symm⟩
      · rintro ⟨v, h1, h2⟩; rw [h1, h2]
    rw [heq]
    exact isOpen_iUnion fun v => (hlc {v}).prod (hlc {v})

  have hφcont : Continuous fun p : G × G => (p.1 * p.2, p.1) :=
    (continuous_fst.mul continuous_snd).prodMk continuous_fst
  have hU : IsOpen {p : G × G | f (p.1 * p.2) = f p.1} :=
    hA.preimage hφcont

  obtain ⟨V, W, hVopen, hWopen, hCV, h1W, hVW⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (1 : G))) hU
      (by
        rintro p ⟨hc, hy⟩
        simp only [Set.mem_singleton_iff] at hy
        simp only [Set.mem_setOf_eq]
        rw [hy, mul_one])
  have hWc : ∀ c ∈ C, ∀ w ∈ W, f (c * w) = f c := by
    intro c hc w hw
    exact hVW (show (c, w) ∈ V ×ˢ W from ⟨hCV hc, hw⟩)

  have hstab : W ∩ W⁻¹ ⊆ (Representation.stabilizer vectorRightTranslation f : Set G) := by
    intro j hj
    change j ∈ Representation.stabilizer vectorRightTranslation f
    rw [Representation.mem_stabilizer]
    ext x
    change f (x * j) = f x
    have hj1 : j ∈ W := hj.1
    have hj2 : j⁻¹ ∈ W := hj.2
    by_cases hx : f x = 0
    ·
      rw [hx]
      by_contra hne
      obtain ⟨b, c, hcC, hxj⟩ := hrep (x * j) hne
      have hx1 : x = (b : G) * (c * j⁻¹) := by
        calc x = x * j * j⁻¹ := by group
          _ = ((b : G) * c) * j⁻¹ := by rw [hxj]
          _ = (b : G) * (c * j⁻¹) := by group
      have hcw : f (c * j⁻¹) = f c := hWc c hcC (j⁻¹) hj2
      have hthis : f x = f (x * j) := by
        calc f x = f ((b : G) * (c * j⁻¹)) := by rw [hx1]
          _ = ρ b (f (c * j⁻¹)) := hcov b (c * j⁻¹)
          _ = ρ b (f c) := by rw [hcw]
          _ = f ((b : G) * c) := (hcov b c).symm
          _ = f (x * j) := by rw [hxj]
      rw [hx] at hthis
      exact hne hthis.symm
    ·
      obtain ⟨b, c, hcC, hxc⟩ := hrep x hx
      calc f (x * j) = f ((b : G) * (c * j)) := by rw [hxc, mul_assoc]
        _ = ρ b (f (c * j)) := hcov b (c * j)
        _ = ρ b (f c) := by rw [hWc c hcC j hj1]
        _ = f ((b : G) * c) := (hcov b c).symm
        _ = f x := by rw [hxc]

  have h1W' : (1 : G) ∈ W := h1W (Set.mem_singleton 1)
  have hJmem : (Representation.stabilizer vectorRightTranslation f : Set G) ∈ 𝓝 (1 : G) :=
    Filter.mem_of_superset
      ((hWopen.inter hWopen.inv).mem_nhds ⟨h1W', by simpa using h1W'⟩) hstab
  have hJopen : IsOpen (Representation.stabilizer vectorRightTranslation f : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ hJmem
  exact ⟨⟨Representation.stabilizer vectorRightTranslation f, hJopen⟩,
    fun j hj => Representation.mem_stabilizer.mp hj⟩

end
end DedekindZetaZeroFree.KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps
