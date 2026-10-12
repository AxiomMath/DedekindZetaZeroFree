module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.SubmodulesAndQuotients

@[expose] public section

namespace DedekindZetaZeroFree
open scoped Topology

section Averaging
variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup V] [Module ℂ V]

structure FiniteAveragingLevel (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (v : V) where
  subgroup : Subgroup U.toOpenSubgroup
  isOpen : IsOpen (subgroup : Set U.toOpenSubgroup)
  isNormal : subgroup.Normal
  finite : Finite (U.toOpenSubgroup ⧸ subgroup)
  fixes : ∀ h : subgroup, ρ (h.val.val : G) v = v

theorem compactOpen_stabilizer_core (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (v : V) (H : OpenSubgroup U.toOpenSubgroup)
    (hH : ∀ h : H, ρ (h.val.val : G) v = v) :
    IsOpen ((H.toSubgroup.normalCore : Subgroup U.toOpenSubgroup) : Set U.toOpenSubgroup) ∧
    Finite (U.toOpenSubgroup ⧸ H.toSubgroup.normalCore) ∧
    (∀ h : H.toSubgroup.normalCore, ρ (h.val.val : G) v = v) := by
  haveI : IsTopologicalGroup ↥U.toOpenSubgroup := by
    change IsTopologicalGroup ↥U.toOpenSubgroup.toSubgroup
    infer_instance
  haveI : CompactSpace U.toOpenSubgroup :=
    isCompact_iff_compactSpace.mp U.isCompact
  haveI : Finite (U.toOpenSubgroup ⧸ H.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen H.toSubgroup H.isOpen
  haveI : Subgroup.FiniteIndex H.toSubgroup := Subgroup.finiteIndex_of_finite_quotient
  haveI : Subgroup.FiniteIndex H.toSubgroup.normalCore := inferInstance
  haveI : Finite (U.toOpenSubgroup ⧸ H.toSubgroup.normalCore) := inferInstance
  refine ⟨?_, inferInstance, ?_⟩
  · exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed _ H.isClosed)
  · intro h
    exact hH ⟨h.val, Subgroup.normalCore_le H.toSubgroup h.property⟩

theorem exists_finiteAveragingLevel (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (v : V) :
    Nonempty (FiniteAveragingLevel ρ U v) := by
  obtain ⟨J, hJ⟩ := hρ v
  let H : OpenSubgroup U.toOpenSubgroup :=
    J.comap U.toOpenSubgroup.subtype continuous_subtype_val
  have hH : ∀ h : H, ρ (h.val.val : G) v = v := by
    intro h
    exact hJ _ h.property
  obtain ⟨hopen, hfin, hfix⟩ := compactOpen_stabilizer_core ρ U v H hH
  exact ⟨{ subgroup := H.toSubgroup.normalCore
           isOpen := hopen
           isNormal := Subgroup.normalCore_normal H.toSubgroup
           finite := hfin
           fixes := hfix }⟩

noncomputable def finiteQuotientAverage (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (K : Subgroup U.toOpenSubgroup)
    [Finite (U.toOpenSubgroup ⧸ K)]
    (r : (U.toOpenSubgroup ⧸ K) → U.toOpenSubgroup) (v : V) : V := by
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K)
  exact (Nat.card (U.toOpenSubgroup ⧸ K) : ℂ)⁻¹ •
    ∑ x : U.toOpenSubgroup ⧸ K, ρ (r x : G) v

private theorem orbit_eq_of_coset_eq (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (v : V) (K : Subgroup U.toOpenSubgroup)
    (hfix : ∀ h : K, ρ (h.val.val : G) v = v)
    (a b : U.toOpenSubgroup) (hab : (QuotientGroup.mk a : U.toOpenSubgroup ⧸ K) = QuotientGroup.mk b) :
    ρ (a : G) v = ρ (b : G) v := by
  have hm := QuotientGroup.eq.mp hab
  have hf := hfix ⟨a⁻¹ * b, hm⟩
  have he := congrArg (ρ (a : G)) hf
  simpa [map_mul, Module.End.mul_apply] using he.symm

noncomputable def finiteAverageMap (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (K : Subgroup U.toOpenSubgroup)
    [Finite (U.toOpenSubgroup ⧸ K)]
    (r : (U.toOpenSubgroup ⧸ K) → U.toOpenSubgroup) : V →ₗ[ℂ] V := by
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K)
  exact (Nat.card (U.toOpenSubgroup ⧸ K) : ℂ)⁻¹ • ∑ x, ρ (r x : G)

private theorem finiteAverageMap_apply (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (K : Subgroup U.toOpenSubgroup)
    [Finite (U.toOpenSubgroup ⧸ K)]
    (r : (U.toOpenSubgroup ⧸ K) → U.toOpenSubgroup) (v : V) :
    finiteAverageMap ρ U K r v = finiteQuotientAverage ρ U K r v := by
  classical
  simp [finiteAverageMap, finiteQuotientAverage, LinearMap.sum_apply]

 theorem finiteAverage_constant (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (K : Subgroup U.toOpenSubgroup)
    [Finite (U.toOpenSubgroup ⧸ K)]
    (r : (U.toOpenSubgroup ⧸ K) → U.toOpenSubgroup) (v : V)
    (hv : ∀ g : U.toOpenSubgroup, ρ (g : G) v = v) :
    finiteQuotientAverage ρ U K r v = v := by
  classical
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K)
  unfold finiteQuotientAverage
  simp only [hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hn : (Nat.card (U.toOpenSubgroup ⧸ K) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [inv_mul_cancel₀ hn, one_smul]

 theorem finiteAverage_left (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (v : V) (K : FiniteAveragingLevel ρ U v)
    (r : (U.toOpenSubgroup ⧸ K.subgroup) → U.toOpenSubgroup)
    (hr : ∀ x, QuotientGroup.mk (r x) = x) (g : U.toOpenSubgroup) :
    letI := K.finite
    ρ (g : G) (finiteQuotientAverage ρ U K.subgroup r v) =
      finiteQuotientAverage ρ U K.subgroup r v := by
  classical
  letI := K.finite
  letI := K.isNormal
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  unfold finiteQuotientAverage
  simp only [map_smul, map_sum]
  congr 1
  let e := Equiv.mulLeft (QuotientGroup.mk g : U.toOpenSubgroup ⧸ K.subgroup)
  calc
    ∑ x, ρ (g : G) (ρ (r x : G) v) = ∑ x, ρ (r (e x) : G) v := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Module.End.mul_apply, ← map_mul]
      apply orbit_eq_of_coset_eq ρ U v K.subgroup K.fixes (g * r x) (r (e x))
      rw [QuotientGroup.mk_mul, hr, hr]
      rfl
    _ = ∑ x, ρ (r x : G) v := Equiv.sum_comp e (fun x => ρ (r x : G) v)

private theorem finiteAverage_right (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (v : V) (K : FiniteAveragingLevel ρ U v)
    (r : (U.toOpenSubgroup ⧸ K.subgroup) → U.toOpenSubgroup)
    (hr : ∀ x, QuotientGroup.mk (r x) = x) (g : U.toOpenSubgroup) :
    letI := K.finite
    finiteQuotientAverage ρ U K.subgroup r (ρ (g : G) v) =
      finiteQuotientAverage ρ U K.subgroup r v := by
  classical
  letI := K.finite
  letI := K.isNormal
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  unfold finiteQuotientAverage
  congr 1
  let e := Equiv.mulRight (QuotientGroup.mk g : U.toOpenSubgroup ⧸ K.subgroup)
  calc
    ∑ x, ρ (r x : G) (ρ (g : G) v) = ∑ x, ρ (r (e x) : G) v := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Module.End.mul_apply, ← map_mul]
      apply orbit_eq_of_coset_eq ρ U v K.subgroup K.fixes (r x * g) (r (e x))
      rw [QuotientGroup.mk_mul, hr, hr]
      rfl
    _ = ∑ x, ρ (r x : G) v := Equiv.sum_comp e (fun x => ρ (r x : G) v)

theorem finiteQuotientAverage_independent (ρ : Representation ℂ G V)
    (U : CompactOpenLevel G) (v : V) (K L : FiniteAveragingLevel ρ U v)
    (r : (U.toOpenSubgroup ⧸ K.subgroup) → U.toOpenSubgroup)
    (s : (U.toOpenSubgroup ⧸ L.subgroup) → U.toOpenSubgroup)
    (hr : ∀ x, QuotientGroup.mk (r x) = x)
    (hs : ∀ x, QuotientGroup.mk (s x) = x) :
    letI := K.finite
    letI := L.finite
    finiteQuotientAverage ρ U K.subgroup r v =
      finiteQuotientAverage ρ U L.subgroup s v := by
  classical
  letI := K.finite
  letI := L.finite
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ L.subgroup)
  let f := finiteAverageMap ρ U K.subgroup r
  have hleft : f (finiteQuotientAverage ρ U L.subgroup s v) =
      finiteQuotientAverage ρ U L.subgroup s v := by
    rw [finiteAverageMap_apply]
    exact finiteAverage_constant ρ U K.subgroup r _ (finiteAverage_left ρ U v L s hs)
  have hright : f (finiteQuotientAverage ρ U L.subgroup s v) =
      finiteQuotientAverage ρ U K.subgroup r v := by
    unfold finiteQuotientAverage
    rw [map_smul, map_sum]
    have hh : ∀ x : U.toOpenSubgroup ⧸ L.subgroup,
        f (ρ (s x : G) v) = f v := by
      intro x
      dsimp [f]
      rw [finiteAverageMap_apply, finiteAverageMap_apply]
      exact finiteAverage_right ρ U v K r hr (s x)
    simp only [hh, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have hn : (Nat.card (U.toOpenSubgroup ⧸ L.subgroup) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    rw [inv_mul_cancel₀ hn, one_smul]
    exact finiteAverageMap_apply ρ U K.subgroup r v
  exact hright.symm.trans hleft

noncomputable def compactOpenAverageFun (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (v : V) : V := by
  let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  letI := K.finite
  exact finiteQuotientAverage ρ U K.subgroup Quotient.out v

private theorem averageFun_eq_level (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (v : V)
    (K : FiniteAveragingLevel ρ U v) :
    letI := K.finite
    compactOpenAverageFun ρ hρ U v = finiteQuotientAverage ρ U K.subgroup Quotient.out v := by
  let L := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  letI := L.finite
  change finiteQuotientAverage ρ U L.subgroup Quotient.out v = _
  exact finiteQuotientAverage_independent ρ U v L K Quotient.out Quotient.out
    (fun x => Quotient.out_eq x) (fun x => Quotient.out_eq x)

noncomputable def commonLevel (ρ : Representation ℂ G V) (U : CompactOpenLevel G)
    (v w : V) (K : FiniteAveragingLevel ρ U v) (L : FiniteAveragingLevel ρ U w) :
    FiniteAveragingLevel ρ U v where
  subgroup := K.subgroup ⊓ L.subgroup
  isOpen := K.isOpen.inter L.isOpen
  isNormal := by
    letI := K.isNormal
    letI := L.isNormal
    infer_instance
  finite := by
    letI : IsTopologicalGroup U.toOpenSubgroup := by
      change IsTopologicalGroup U.toOpenSubgroup.toSubgroup
      infer_instance
    letI : CompactSpace U.toOpenSubgroup := isCompact_iff_compactSpace.mp U.isCompact
    exact Subgroup.quotient_finite_of_isOpen _ (K.isOpen.inter L.isOpen)
  fixes := fun h => K.fixes ⟨h.val, h.property.1⟩

theorem compactOpenAverageFun_add (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (v w : V) :
    compactOpenAverageFun ρ hρ U (v + w) =
      compactOpenAverageFun ρ hρ U v + compactOpenAverageFun ρ hρ U w := by
  classical
  let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  let L := Classical.choice (exists_finiteAveragingLevel ρ hρ U w)
  let M := commonLevel ρ U v w K L
  let N : FiniteAveragingLevel ρ U w :=
    { M with fixes := fun h => L.fixes ⟨h.val, h.property.2⟩ }
  let P : FiniteAveragingLevel ρ U (v + w) :=
    { M with fixes := fun h => by simp only [map_add, M.fixes h, N.fixes h] }
  letI := M.finite
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ M.subgroup)
  rw [averageFun_eq_level ρ hρ U (v + w) P, averageFun_eq_level ρ hρ U v M,
    averageFun_eq_level ρ hρ U w N]
  unfold finiteQuotientAverage
  simp only [map_add, Finset.sum_add_distrib, smul_add]
  rfl

theorem compactOpenAverageFun_smul (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (a : ℂ) (v : V) :
    compactOpenAverageFun ρ hρ U (a • v) = a • compactOpenAverageFun ρ hρ U v := by
  classical
  let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  let L : FiniteAveragingLevel ρ U (a • v) :=
    { K with fixes := fun h => by simp only [map_smul, K.fixes h] }
  letI := K.finite
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  rw [averageFun_eq_level ρ hρ U (a • v) L, averageFun_eq_level ρ hρ U v K]
  unfold finiteQuotientAverage
  simp only [map_smul, ← Finset.smul_sum]
  exact smul_comm _ a _

noncomputable def compactOpenAverage (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) : V →ₗ[ℂ] V where
  toFun := compactOpenAverageFun ρ hρ U
  map_add' := compactOpenAverageFun_add ρ hρ U
  map_smul' := compactOpenAverageFun_smul ρ hρ U

theorem compactOpenAverage_eq_finite (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (v : V)
    (K : FiniteAveragingLevel ρ U v)
    (r : (U.toOpenSubgroup ⧸ K.subgroup) → U.toOpenSubgroup)
    (hr : ∀ x, QuotientGroup.mk (r x) = x) :
    letI := K.finite
    compactOpenAverage ρ hρ U v = finiteQuotientAverage ρ U K.subgroup r v := by
  let L := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  letI := L.finite
  change finiteQuotientAverage ρ U L.subgroup Quotient.out v = _
  exact finiteQuotientAverage_independent ρ U v L K Quotient.out r
    (fun x => Quotient.out_eq x) hr

theorem compactOpenAverage_fixed (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) (v : V)
    (hv : v ∈ fixedSubmodule ρ U.toOpenSubgroup.toSubgroup) :
    compactOpenAverage ρ hρ U v = v := by
  classical
  let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  letI := K.finite
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  rw [compactOpenAverage_eq_finite ρ hρ U v K Quotient.out (fun x => Quotient.out_eq x)]
  unfold finiteQuotientAverage
  have hf : ∀ x : U.toOpenSubgroup ⧸ K.subgroup,
      ρ ((Quotient.out x : U.toOpenSubgroup) : G) v = v :=
    fun x => hv (Quotient.out x)
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hn : (Nat.card (U.toOpenSubgroup ⧸ K.subgroup) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [inv_mul_cancel₀ hn, one_smul]

theorem compactOpenAverage_range (ρ : Representation ℂ G V)
    (hρ : SmoothRepresentation ρ) (U : CompactOpenLevel G) :
    (compactOpenAverage ρ hρ U).range = fixedSubmodule ρ U.toOpenSubgroup.toSubgroup := by
  classical
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
    letI := K.finite
    letI := K.isNormal
    letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
    rw [compactOpenAverage_eq_finite ρ hρ U v K Quotient.out (fun x => Quotient.out_eq x)]
    intro u
    unfold finiteQuotientAverage
    simp only [map_smul, map_sum]
    congr 1
    let e := Equiv.mulLeft (QuotientGroup.mk u : U.toOpenSubgroup ⧸ K.subgroup)
    calc
      ∑ x : U.toOpenSubgroup ⧸ K.subgroup, ρ (u : G) (ρ ((Quotient.out x : U.toOpenSubgroup) : G) v) =
          ∑ x : U.toOpenSubgroup ⧸ K.subgroup, ρ ((Quotient.out (e x) : U.toOpenSubgroup) : G) v := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Module.End.mul_apply, ← map_mul]
        exact orbit_eq_of_coset_eq ρ U v K.subgroup K.fixes
          (u * Quotient.out x) (Quotient.out (e x)) (by
            rw [QuotientGroup.mk_mul]
            simp only [QuotientGroup.mk, Quotient.out_eq]
            rfl)
      _ = ∑ x : U.toOpenSubgroup ⧸ K.subgroup, ρ ((Quotient.out x : U.toOpenSubgroup) : G) v :=
        Equiv.sum_comp e (fun x => ρ ((Quotient.out x : U.toOpenSubgroup) : G) v)
  · intro v hv
    exact ⟨v, compactOpenAverage_fixed ρ hρ U v hv⟩

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem compactOpenAverage_natural (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρ : SmoothRepresentation ρ)
    (hσ : SmoothRepresentation σ) (U : CompactOpenLevel G)
    (q : Representation.IntertwiningMap ρ σ) :
    q.toLinearMap.comp (compactOpenAverage ρ hρ U) =
      (compactOpenAverage σ hσ U).comp q.toLinearMap := by
  classical
  apply LinearMap.ext
  intro v
  let K := Classical.choice (exists_finiteAveragingLevel ρ hρ U v)
  let L : FiniteAveragingLevel σ U (q v) :=
    { subgroup := K.subgroup
      isOpen := K.isOpen
      isNormal := K.isNormal
      finite := K.finite
      fixes := fun h => by rw [← q.isIntertwining, K.fixes h] }
  letI := K.finite
  letI := Fintype.ofFinite (U.toOpenSubgroup ⧸ K.subgroup)
  change q (compactOpenAverage ρ hρ U v) = compactOpenAverage σ hσ U (q v)
  rw [compactOpenAverage_eq_finite ρ hρ U v K Quotient.out (fun x => Quotient.out_eq x),
    compactOpenAverage_eq_finite σ hσ U (q v) L Quotient.out (fun x => Quotient.out_eq x)]
  unfold finiteQuotientAverage
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact Representation.IntertwiningMap.isIntertwining ρ σ q
    ((Quotient.out x : U.toOpenSubgroup) : G) v

def fixedSpaceMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (q : Representation.IntertwiningMap ρ σ) (U : Subgroup G) :
    fixedSubmodule ρ U →ₗ[ℂ] fixedSubmodule σ U :=
  (q.toLinearMap.comp (fixedSubmodule ρ U).subtype).codRestrict _ (by
    intro v
    exact intertwiningMap_fixedSubmodule ρ σ q U ⟨v.val, v.property, rfl⟩)

theorem fixedSpaceMap_surjective (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hρ : SmoothRepresentation ρ)
    (hσ : SmoothRepresentation σ) (U : CompactOpenLevel G)
    (q : Representation.IntertwiningMap ρ σ) (hq : Function.Surjective q) :
    Function.Surjective (fixedSpaceMap ρ σ q U.toOpenSubgroup.toSubgroup) := by
  intro w
  obtain ⟨v, hv⟩ := hq w.val
  have hav : compactOpenAverage ρ hρ U v ∈ fixedSubmodule ρ U.toOpenSubgroup.toSubgroup := by
    rw [← compactOpenAverage_range ρ hρ U]
    exact LinearMap.mem_range_self _ v
  refine ⟨⟨compactOpenAverage ρ hρ U v, hav⟩, ?_⟩
  apply Subtype.ext
  change q (compactOpenAverage ρ hρ U v) = w.val
  have hn := LinearMap.congr_fun (compactOpenAverage_natural ρ σ hρ hσ U q) v
  change q (compactOpenAverage ρ hρ U v) = compactOpenAverage σ hσ U (q v) at hn
  rw [hn, hv]
  exact compactOpenAverage_fixed σ hσ U w.val w.property

end Averaging

end DedekindZetaZeroFree
