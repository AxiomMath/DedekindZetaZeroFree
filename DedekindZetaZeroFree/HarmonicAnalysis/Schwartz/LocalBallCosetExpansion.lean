module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.BallQuotients

@[expose] public section

noncomputable section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

private theorem containing_ball (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (hf : HasCompactSupport f) :
    ∃ r : ℤ, tsupport f ⊆ (finiteCompletionBall F v r : Set (v.adicCompletion F)) := by
  obtain ⟨k, hk⟩ := hf.elim_directed_cover
    (fun k : ℕ => (finiteCompletionBall F v (-(k : ℤ)) : Set (v.adicCompletion F)))
    (fun k => isOpen_finiteCompletionBall F v _)
    (by rw [iUnion_finiteCompletionBall_neg_nat F v]; exact Set.subset_univ _)
    (by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · exact (finiteCompletionBall_le_iff F v _ _).2 (by omega)
      · exact (finiteCompletionBall_le_iff F v _ _).2 (by omega))
  exact ⟨_, hk⟩

private theorem uniform_ball (v : HeightOneSpectrum (𝓞 F))
    (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f)
    (r : ℤ) (hr : tsupport f ⊆ (finiteCompletionBall F v r : Set (v.adicCompletion F))) :
    ∃ n : ℤ, r ≤ n ∧ ∀ x u, u ∈ finiteCompletionBall F v n → f (x + u) = f x := by
  have hl : ∀ b : v.adicCompletion F, ∃ n : ℤ,
      ∀ x, x - b ∈ finiteCompletionBall F v n → f x = f b := by
    intro b
    obtain ⟨n, _, hn⟩ := (finiteCompletionBall_hasBasis_nhds F v b).mem_iff.mp
      (hf.eventually_eq b)
    exact ⟨n, fun x hx => hn hx⟩
  choose d hd using hl
  let B := finiteCompletionBall F v r
  obtain ⟨T, hT⟩ := (isCompact_finiteCompletionBall F v r).elim_finite_subcover
    (fun b : B => {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v (d b)})
    (fun b => isOpen_finiteCompletionBall_coset F v b (d b))
    (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  let n : ℤ := max r ((T.sup (fun b => (d b).toNat) : ℕ) : ℤ)
  have hrn : r ≤ n := le_max_left _ _
  have hdn : ∀ b ∈ T, d b ≤ n := by
    intro b hb
    have := Finset.le_sup (f := fun b : B => (d b).toNat) hb
    dsimp [n]
    omega
  refine ⟨n, hrn, ?_⟩
  intro x u hu
  have hur : u ∈ B := (finiteCompletionBall_le_iff F v r n).2 hrn hu
  by_cases hx : x ∈ B
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hT hx)
    obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hb
    have hud : u ∈ finiteCompletionBall F v (d b) :=
      (finiteCompletionBall_le_iff F v (d b) n).2 (hdn b hb) hu
    have hxub : x + u - b ∈ finiteCompletionBall F v (d b) := by
      convert (finiteCompletionBall F v (d b)).add_mem hxb hud using 1 <;> abel
    exact (hd b (x + u) hxub).trans (hd b x hxb).symm
  · have hxu : x + u ∉ B := by
      intro h
      apply hx
      convert B.sub_mem h hur using 1 <;> abel
    rw [image_eq_zero_of_notMem_tsupport (fun h => hxu (hr h)),
      image_eq_zero_of_notMem_tsupport (fun h => hx (hr h))]

private theorem transversal (v : HeightOneSpectrum (𝓞 F)) (r n : ℤ) (hrn : r ≤ n) :
    ∃ T : Finset (v.adicCompletion F),
      (↑T : Set (v.adicCompletion F)) ⊆ (finiteCompletionBall F v r : Set (v.adicCompletion F)) ∧
      (∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint
        {x : v.adicCompletion F | x - t ∈ finiteCompletionBall F v n}
        {x : v.adicCompletion F | x - s ∈ finiteCompletionBall F v n}) ∧
      (finiteCompletionBall F v r : Set (v.adicCompletion F)) =
        ⋃ t ∈ T, {x : v.adicCompletion F | x - t ∈ finiteCompletionBall F v n} := by
  classical
  let B := finiteCompletionBall F v r
  let U := finiteCompletionBall F v n
  let Q := finiteCompletionBallQuotient F v r n
  letI : Finite Q := finite_finiteCompletionBallQuotient F v r n hrn
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → v.adicCompletion F := fun q => q.out.val
  have hrep : ∀ q : Q, (QuotientAddGroup.mk q.out : Q) = q := fun q => Quotient.out_eq' q
  let T := Finset.univ.image rep
  have hT : ∀ t ∈ T, ∃ q : Q, rep q = t := by
    intro t ht
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp ht
    exact ⟨q, hq⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, rfl⟩ := hT t ht
    exact q.out.property
  · intro t ht s hs hts
    obtain ⟨q, rfl⟩ := hT t ht
    obtain ⟨p, rfl⟩ := hT s hs
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hsub : rep q - rep p ∈ U := by
      convert U.sub_mem hy hx using 1 <;> abel
    have heq : q = p := by
      rw [← hrep q, ← hrep p]
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      exact hsub
    exact hts (congrArg rep heq)
  · apply Set.Subset.antisymm
    · intro x hx
      let a : B := ⟨x, hx⟩
      let q : Q := QuotientAddGroup.mk a
      apply Set.mem_iUnion.mpr
      refine ⟨rep q, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
      · have heq : (QuotientAddGroup.mk a : Q) = QuotientAddGroup.mk q.out := (hrep q).symm
        exact QuotientAddGroup.eq_iff_sub_mem.mp heq
    · intro x hx
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx
      obtain ⟨ht, hxt⟩ := Set.mem_iUnion.mp ht
      obtain ⟨q, rfl⟩ := hT t ht
      have hU : U ≤ B := (finiteCompletionBall_le_iff F v r n).2 hrn
      have h := B.add_mem (hU hxt) q.out.property
      change x - rep q + rep q ∈ B at h
      change x ∈ finiteCompletionBall F v r
      simpa only [sub_add_cancel] using h

theorem localSchwartz_finite_ball_coset_expansion
    (v : HeightOneSpectrum (𝓞 F)) (f : v.adicCompletion F → ℂ)
    (hf : f ∈ localSchwartz F v) :
    ∃ (r n : ℤ) (T : Finset (v.adicCompletion F)),
      r ≤ n ∧
      tsupport f ⊆ (finiteCompletionBall F v r : Set (v.adicCompletion F)) ∧
      (↑T : Set (v.adicCompletion F)) ⊆
        (finiteCompletionBall F v r : Set (v.adicCompletion F)) ∧
      (∀ t ∈ T, ∀ s ∈ T, t ≠ s → Disjoint
        {x : v.adicCompletion F | x - t ∈ finiteCompletionBall F v n}
        {x : v.adicCompletion F | x - s ∈ finiteCompletionBall F v n}) ∧
      (finiteCompletionBall F v r : Set (v.adicCompletion F)) =
        (⋃ t ∈ T, {x : v.adicCompletion F | x - t ∈ finiteCompletionBall F v n}) ∧
      (∀ x u : v.adicCompletion F, u ∈ finiteCompletionBall F v n →
        f (x + u) = f x) ∧
      (∀ x : v.adicCompletion F,
        f x = ∑ t ∈ T, f t * localCosetIndicator F v t (finiteCompletionBall F v n) x) := by
  classical
  obtain ⟨r, hr⟩ := containing_ball F v f hf.2
  obtain ⟨n, hrn, hinv⟩ := uniform_ball F v f hf.1 r hr
  obtain ⟨T, hT, hdisj, hcover⟩ := transversal F v r n hrn
  refine ⟨r, n, T, hrn, hr, hT, hdisj, hcover, hinv, ?_⟩
  intro x
  by_cases hx : x ∈ finiteCompletionBall F v r
  · have hx' : x ∈ (finiteCompletionBall F v r : Set (v.adicCompletion F)) := hx
    rw [hcover] at hx'
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨ht, hxt⟩ := Set.mem_iUnion.mp ht
    change x - t ∈ finiteCompletionBall F v n at hxt
    have hft : f x = f t := by
      have h := hinv t (x - t) hxt
      simpa only [add_sub_cancel] using h
    rw [Finset.sum_eq_single_of_mem t ht]
    · simp only [localCosetIndicator_apply, if_pos hxt, mul_one, hft]
    · intro s hs hst
      have hxs : x - s ∉ finiteCompletionBall F v n :=
        fun h => (Set.disjoint_left.mp (hdisj t ht s hs hst.symm)) hxt h
      simp only [localCosetIndicator_apply, if_neg hxs, mul_zero]
  · have hfzero : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hr h))
    rw [hfzero]
    symm
    apply Finset.sum_eq_zero
    intro t ht
    have hxt : x - t ∉ finiteCompletionBall F v n := by
      intro h
      apply hx
      change x ∈ (finiteCompletionBall F v r : Set (v.adicCompletion F))
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht, h⟩⟩
    simp only [localCosetIndicator_apply, if_neg hxt, mul_zero]

theorem localCosetIndicator_ball_mem_localSchwartz
    (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletion F) (n : ℤ) :
    localCosetIndicator F v b (finiteCompletionBall F v n) ∈ localSchwartz F v := by
  let S : Set (v.adicCompletion F) :=
    {x | x - b ∈ finiteCompletionBall F v n}
  have hc : IsCompact S := isCompact_finiteCompletionBall_coset F v b n
  have hcl : IsClopen S := ⟨hc.isClosed, isOpen_finiteCompletionBall_coset F v b n⟩
  refine ⟨?_, ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant
  · apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hcl.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp [localCosetIndicator, S] at hn ⊢; exact hn)

end DedekindZetaZeroFree

end
