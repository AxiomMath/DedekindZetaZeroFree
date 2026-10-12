module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCoinvariants.TransversalAverages

open ValuativeRel

private lemma compact_bound {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (S : Set K) (hS : IsCompact S) :
    ∃ γ : (ValueGroupWithZero K)ˣ, S ⊆ {x | valuation K x ≤ γ} := by
  let v := valuation K
  have hopen (γ : (ValueGroupWithZero K)ˣ) : IsOpen {x | v x ≤ γ} := by
    obtain ⟨z, hz⟩ := valuation_surjective (γ : ValueGroupWithZero K)
    have hz0 : z ≠ 0 := by
      intro h
      exact γ.ne_zero (by simpa [h] using hz.symm)
    have ho := Valuation.isOpen_closedBall (v := v) (r := v.restrict z)
      (by simpa using hz0)
    convert ho using 1
    ext x
    change v x ≤ (γ : ValueGroupWithZero K) ↔ v.restrict x ≤ v.restrict z
    rw [Valuation.restrict_le_iff, hz]
  apply hS.elim_directed_cover (fun γ : (ValueGroupWithZero K)ˣ => {x | v x ≤ γ}) hopen
  · intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨Units.mk0 (max (v x) 1)
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))), ?_⟩
    exact le_max_left (v x) 1
  · intro a b
    refine ⟨if a ≤ b then b else a, ?_, ?_⟩
    · intro x hx
      split_ifs with h
      · exact le_trans (show v x ≤ a from hx) (show (a : ValueGroupWithZero K) ≤ b from h)
      · exact hx
    · intro x hx
      split_ifs with h
      · exact hx
      · exact le_trans (show v x ≤ b from hx)
          (show (b : ValueGroupWithZero K) ≤ a from le_of_not_ge h)

private lemma finite_transversal {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    (J L : AddSubgroup K) (hJo : IsOpen (J : Set K)) (hLc : IsCompact (L : Set K)) :
    ∃ R : Finset K, (∀ r ∈ R, r ∈ L) ∧
      (∀ l ∈ L, ∃! r : {r // r ∈ R}, l - r.val ∈ J) ∧ R.Nonempty := by
  classical
  let mk : K → K ⧸ J := QuotientAddGroup.mk
  let Q : Set (K ⧸ J) := mk '' (L : Set K)
  letI : DiscreteTopology (K ⧸ J) := QuotientAddGroup.discreteTopology hJo
  have hQ : Q.Finite := (hLc.image QuotientAddGroup.continuous_mk).finite_of_discrete
  letI : Finite Q := hQ.to_subtype
  have hex (q : Q) : ∃ r : K, r ∈ L ∧ mk r = q.val := q.property
  let rep (q : Q) : K := Classical.choose (hex q)
  have hrep (q : Q) : rep q ∈ L ∧ mk (rep q) = q.val := Classical.choose_spec (hex q)
  have hR : (Set.range rep).Finite := Set.finite_range rep
  let R := hR.toFinset
  have hmem (r : K) : r ∈ R ↔ ∃ q : Q, rep q = r := by simp [R]
  refine ⟨R, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨q, rfl⟩ := (hmem r).mp hr
    exact (hrep q).1
  · intro l hl
    let q : Q := ⟨mk l, ⟨l, hl, rfl⟩⟩
    have hr : rep q ∈ R := (hmem _).mpr ⟨q, rfl⟩
    refine ⟨⟨rep q, hr⟩, ?_, ?_⟩
    · apply QuotientAddGroup.eq_iff_sub_mem.mp
      exact (hrep q).2.symm
    · intro r hr'
      obtain ⟨q', hq'⟩ := (hmem r.val).mp r.property
      have heq : q' = q := by
        apply Subtype.ext
        change q'.val = mk l
        rw [← (hrep q').2, hq']
        exact (QuotientAddGroup.eq_iff_sub_mem.mpr hr').symm
      apply Subtype.ext
      change r.val = rep q
      rw [← hq', heq]
  · let q : Q := ⟨mk 0, ⟨0, L.zero_mem, rfl⟩⟩
    exact ⟨rep q, (hmem _).mpr ⟨q, rfl⟩⟩

theorem compactOpen_enlargement_transversal
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (J : AddSubgroup K) (hJo : IsOpen (J : Set K))
    (hJc : IsCompact (J : Set K)) (F : Finset K) :
    ∃ L : AddSubgroup K, ∃ R : Finset K,
      IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧ J ≤ L ∧
      (∀ n ∈ F, n ∈ L) ∧
      ((∀ r ∈ R, r ∈ L) ∧
        ∀ l ∈ L, ∃! r : {r // r ∈ R}, l - r.val ∈ J) ∧
      R.Nonempty := by
  classical
  obtain ⟨γ, hγ⟩ := compact_bound ((J : Set K) ∪ (F : Set K))
    (hJc.union F.finite_toSet.isCompact)
  let L := (valuation K).leAddSubgroup (γ : ValueGroupWithZero K)
  have hJL : J ≤ L := fun x hx => hγ (Or.inl hx)
  have hLF : ∀ n ∈ F, n ∈ L := fun n hn => hγ (Or.inr hn)
  have hLo : IsOpen (L : Set K) := AddSubgroup.isOpen_mono hJL hJo
  have hLc : IsCompact (L : Set K) :=
    IsNonarchimedeanLocalField.isCompact_closedBall K γ
  obtain ⟨R, hRL, huniq, hRne⟩ := finite_transversal J L hJo hLc
  exact ⟨L, R, hLo, hLc, hJL, hLF, ⟨hRL, huniq⟩, hRne⟩

end DedekindZetaZeroFree.KPCoinvariants.TransversalAverages

end

section

namespace DedekindZetaZeroFree.KPCoinvariants.TransversalAverages

theorem transversal_average_kills_relation
    {A V : Type*} [AddCommGroup A] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative A) V)
    (ψ : Multiplicative A →* ℂˣ) (J L : AddSubgroup A)
    (hJL : J ≤ L) (R : Finset A)
    (hR : (∀ r ∈ R, r ∈ L) ∧
      ∀ l ∈ L, ∃! r : {r // r ∈ R}, l - r.val ∈ J)
    (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1)
    (n : A) (hn : n ∈ L) (v : V)
    (hv : ∀ j ∈ J, ρ (Multiplicative.ofAdd j) v = v) :
    ((R.card : ℂ)⁻¹ • ∑ r ∈ R,
      ((ψ (Multiplicative.ofAdd r) : ℂ)⁻¹ • ρ (Multiplicative.ofAdd r)))
      (ρ (Multiplicative.ofAdd n) v - (ψ (Multiplicative.ofAdd n) : ℂ) • v) = 0 := by
  classical
  let T := {r // r ∈ R}
  have hex (r : T) : ∃! s : T, r.val + n - s.val ∈ J :=
    hR.2 (r.val + n) (L.add_mem (hR.1 r.val r.property) hn)
  let p : T → T := fun r => Classical.choose (hex r).exists
  have hp (r : T) : r.val + n - (p r).val ∈ J :=
    Classical.choose_spec (hex r).exists
  have hpinj : Function.Injective p := by
    intro a b hab
    have hd : a.val - b.val ∈ J := by
      have hd' := J.sub_mem (hp a) (hp b)
      rw [hab] at hd'
      convert hd' using 1 <;> abel
    exact (hR.2 a.val (hR.1 a.val a.property)).unique
      (by simp) hd
  have hpbij : Function.Bijective p :=
    ⟨hpinj, Finite.surjective_of_injective hpinj⟩
  have hrepr (a b : A) (hab : a - b ∈ J) :
      ρ (Multiplicative.ofAdd a) v = ρ (Multiplicative.ofAdd b) v := by
    have heq : a = b + (a - b) := by abel
    rw [heq, ofAdd_add, map_mul, Module.End.mul_apply,
      hv (a - b) hab]
  have hchar (a b : A) (hab : a - b ∈ J) :
      ψ (Multiplicative.ofAdd a) = ψ (Multiplicative.ofAdd b) := by
    have heq : a = b + (a - b) := by abel
    rw [heq, ofAdd_add, map_mul, hψJ (a - b) hab, mul_one]
  have hsum :
      (∑ r ∈ R, (ψ (Multiplicative.ofAdd r) : ℂ)⁻¹ •
        ρ (Multiplicative.ofAdd r) (ρ (Multiplicative.ofAdd n) v)) =
      (ψ (Multiplicative.ofAdd n) : ℂ) •
        ∑ r ∈ R, (ψ (Multiplicative.ofAdd r) : ℂ)⁻¹ •
          ρ (Multiplicative.ofAdd r) v := by
    rw [Finset.smul_sum]
    rw [← Finset.sum_coe_sort R (fun r =>
      (ψ (Multiplicative.ofAdd r) : ℂ)⁻¹ •
        ρ (Multiplicative.ofAdd r) (ρ (Multiplicative.ofAdd n) v)),
      ← Finset.sum_coe_sort R (fun r =>
        (ψ (Multiplicative.ofAdd n) : ℂ) •
          ((ψ (Multiplicative.ofAdd r) : ℂ)⁻¹ • ρ (Multiplicative.ofAdd r) v))]
    apply Fintype.sum_bijective p hpbij
    intro r
    have hc : (ψ (Multiplicative.ofAdd (p r).val) : ℂ) =
        (ψ (Multiplicative.ofAdd r.val) : ℂ) * (ψ (Multiplicative.ofAdd n) : ℂ) := by
      rw [← hchar (r.val + n) (p r).val (hp r), ofAdd_add,
        map_mul, Units.val_mul]
    rw [← Module.End.mul_apply, ← map_mul, ← ofAdd_add,
      hrepr (r.val + n) (p r).val (hp r), hc, smul_smul]
    simp [mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_sub, map_smul,
    smul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  simp [smul_smul, mul_comm, mul_left_comm, mul_assoc, Finset.smul_sum]

end DedekindZetaZeroFree.KPCoinvariants.TransversalAverages

end

section

namespace DedekindZetaZeroFree.KPCoinvariants.TransversalAverages

theorem coinvariants_map_injective_of_annihilating_averages
    {A U V : Type*} [AddCommGroup A]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative A) U)
    (τ : Representation ℂ (Multiplicative A) V)
    (i : Representation.IntertwiningMap ρ τ) (hi : Function.Injective i)
    (hkill : ∀ v : V, v ∈ Representation.Coinvariants.ker τ →
      ∃ R : Finset A, R.Nonempty ∧
        ((R.card : ℂ)⁻¹ • ∑ n ∈ R, τ (Multiplicative.ofAdd n)) v = 0) :
    Function.Injective (Representation.Coinvariants.map ρ τ i) := by
  classical
  intro x y hxy
  obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective ρ x
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ y
  have hrel : i (u - v) ∈ Representation.Coinvariants.ker τ := by
    apply (Representation.Coinvariants.mk_eq_zero τ).mp
    simpa only [map_sub, Representation.Coinvariants.map_mk, sub_eq_zero] using hxy
  obtain ⟨R, hR, hkillR⟩ := hkill (i (u - v)) hrel
  have hcard : (R.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hR)
  have havg : ((R.card : ℂ)⁻¹ • ∑ n ∈ R, ρ (Multiplicative.ofAdd n)) (u - v) = 0 := by
    apply hi
    simpa only [map_zero, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
      map_sum, i.isIntertwining] using hkillR
  have hclass :
      Representation.Coinvariants.mk ρ
        (((R.card : ℂ)⁻¹ • ∑ n ∈ R, ρ (Multiplicative.ofAdd n)) (u - v)) =
      Representation.Coinvariants.mk ρ (u - v) := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
      Representation.Coinvariants.mk_self_apply, Finset.sum_const]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  apply (Representation.Coinvariants.mk_eq_iff ρ).mpr
  apply (Representation.Coinvariants.mk_eq_zero ρ).mp
  rw [← hclass, havg, map_zero]

end DedekindZetaZeroFree.KPCoinvariants.TransversalAverages

end

section

namespace DedekindZetaZeroFree.KPCoinvariants
variable {K V W : Type*} [Field K] [TopologicalSpace K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

def IsSmooth (ρ : Representation ℂ (Multiplicative K) V) : Prop :=
  ∀ v, IsOpen {n : K | ρ (Multiplicative.ofAdd n) v = v}

noncomputable def twistedRepresentation (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) : Representation ℂ (Multiplicative K) V where
  toFun n := (ψ n : ℂ)⁻¹ • ρ n
  map_one' := by simp
  map_mul' n m := by ext v; simp [map_mul, mul_smul]

abbrev Coinvariants (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) :=
  Representation.Coinvariants (twistedRepresentation ρ ψ)

noncomputable def map (ρ : Representation ℂ (Multiplicative K) V)
    (τ : Representation ℂ (Multiplicative K) W) (ψ : Multiplicative K →* ℂˣ)
    (f : Representation.IntertwiningMap ρ τ) : Coinvariants ρ ψ →ₗ[ℂ] Coinvariants τ ψ :=
  Representation.Coinvariants.map _ _
    { toLinearMap := f.toLinearMap
      isIntertwining' n := by ext v; simp [twistedRepresentation, f.isIntertwining] }

noncomputable def psiAverage (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (R : Finset K) : V →ₗ[ℂ] V :=
  (R.card : ℂ)⁻¹ • ∑ n ∈ R, ((ψ (Multiplicative.ofAdd n) : ℂ)⁻¹ • ρ (Multiplicative.ofAdd n))

def IsTransversal (J L : AddSubgroup K) (R : Finset K) : Prop :=
  (∀ r ∈ R, r ∈ L) ∧
  ∀ l ∈ L, ∃! r : {r // r ∈ R}, l - r.val ∈ J

variable {K U V W : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

theorem commonLevel (ρ : Representation ℂ (Multiplicative K) V)
    (hρ : IsSmooth ρ) (ψ : Multiplicative K →* ℂˣ)
    (hψc : Continuous ψ) (hψs : IsLocallyConstant ψ)
    (T : Finset V) :
    ∃ J : AddSubgroup K, IsOpen (J : Set K) ∧ IsCompact (J : Set K) ∧
      (∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) ∧
      (∀ v ∈ T, ∀ j ∈ J, ρ (Multiplicative.ofAdd j) v = v) := by
  classical
  let O : Set K := {j | ψ (Multiplicative.ofAdd j) = 1} ∩
    ⋂ v ∈ T, {j | ρ (Multiplicative.ofAdd j) v = v}
  have hO : IsOpen O :=
    ((hψs.isOpen_fiber 1).preimage continuous_ofAdd).inter
      (isOpen_biInter_finset fun v _ => hρ v)
  have h0 : (0 : K) ∈ O := by simp [O]
  obtain ⟨γ, _, hγ⟩ :=
    (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mp (hO.mem_nhds h0)
  obtain ⟨t, ht0, ht⟩ := Valuation.IsNontrivial.exists_lt_one
    (v := ValuativeRel.valuation K)
  let β := (γ : ValuativeRel.ValueGroupWithZero K) * ValuativeRel.valuation K t
  have hβ0 : β ≠ 0 := mul_ne_zero (Units.ne_zero γ) (by simpa using ht0)
  have hβγ : β < (γ : ValuativeRel.ValueGroupWithZero K) := by
    simpa [β] using mul_lt_mul_of_pos_left ht (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  let J := (ValuativeRel.valuation K).leAddSubgroup β
  have hJO : (J : Set K) ⊆ O := fun j hj => hγ (hj.trans_lt hβγ)
  have hJopen : IsOpen (J : Set K) := by
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective β
    change IsOpen {x | ValuativeRel.valuation K x ≤ β}
    rw [← ha]
    simp_rw [← (ValuativeRel.valuation K).restrict_le_iff]
    apply Valuation.isOpen_closedBall
    simpa [← ha] using hβ0
  refine ⟨J, hJopen, IsNonarchimedeanLocalField.isCompact_closedBall K β, ?_, ?_⟩
  · intro j hj
    exact (hJO hj).1
  · intro v hv j hj
    exact Set.mem_iInter.mp (Set.mem_iInter.mp (hJO hj).2 v) hv

theorem killsFiniteRelations (ρ : Representation ℂ (Multiplicative K) V)
    (hρ : IsSmooth ρ) (ψ : Multiplicative K →* ℂˣ)
    (hψc : Continuous ψ) (hψs : IsLocallyConstant ψ)
    (S : Finset (K × V)) :
    ∃ J L : AddSubgroup K, ∃ R : Finset K,
      IsOpen (J : Set K) ∧ IsCompact (J : Set K) ∧
      IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧ J ≤ L ∧
      IsTransversal J L R ∧ R.Nonempty ∧
      (∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) ∧
      (∀ nv ∈ S, nv.1 ∈ L ∧ ∀ j ∈ J, ρ (Multiplicative.ofAdd j) nv.2 = nv.2) ∧
      (∀ nv ∈ S, psiAverage ρ ψ R
        (ρ (Multiplicative.ofAdd nv.1) nv.2 - (ψ (Multiplicative.ofAdd nv.1) : ℂ) • nv.2) = 0) := by
  classical
  obtain ⟨J, hJo, hJc, hψJ, hfix⟩ :=
    commonLevel ρ hρ ψ hψc hψs (S.image Prod.snd)
  obtain ⟨L, R, hLo, hLc, hJL, hcontains, hR, hRne⟩ :=
    TransversalAverages.compactOpen_enlargement_transversal J hJo hJc (S.image Prod.fst)
  refine ⟨J, L, R, hJo, hJc, hLo, hLc, hJL, hR, hRne, hψJ, ?_, ?_⟩
  · intro nv hnv
    exact ⟨hcontains nv.1 (Finset.mem_image.mpr ⟨nv, hnv, rfl⟩),
      hfix nv.2 (Finset.mem_image.mpr ⟨nv, hnv, rfl⟩)⟩
  · intro nv hnv
    exact TransversalAverages.transversal_average_kills_relation ρ ψ J L hJL R hR hψJ
      nv.1 (hcontains nv.1 (Finset.mem_image.mpr ⟨nv, hnv, rfl⟩)) nv.2
      (hfix nv.2 (Finset.mem_image.mpr ⟨nv, hnv, rfl⟩))

theorem killsRelation (ρ : Representation ℂ (Multiplicative K) V)
    (hρ : IsSmooth ρ) (ψ : Multiplicative K →* ℂˣ)
    (hψc : Continuous ψ) (hψs : IsLocallyConstant ψ)
    (v : V) (hv : v ∈ Representation.Coinvariants.ker (twistedRepresentation ρ ψ)) :
    ∃ J L : AddSubgroup K, ∃ R : Finset K,
      IsOpen (J : Set K) ∧ IsCompact (J : Set K) ∧
      IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧ J ≤ L ∧
      IsTransversal J L R ∧ R.Nonempty ∧
      (∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) ∧
      (∀ j ∈ J, ρ (Multiplicative.ofAdd j) v = v) ∧
      psiAverage ρ ψ R v = 0 := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  let f : Multiplicative K × V → K × V :=
    fun nv => (Multiplicative.toAdd nv.1, (ψ nv.1 : ℂ)⁻¹ • nv.2)
  obtain ⟨J, L, R, hJo, hJc, hLo, hLc, hJL, hR, hRne, hψJ, hfix, hkill⟩ :=
    killsFiniteRelations ρ hρ ψ hψc hψs (insert (0, v) (c.support.image f))
  refine ⟨J, L, R, hJo, hJc, hLo, hLc, hJL, hR, hRne, hψJ, ?_, ?_⟩
  · exact (hfix (0, v) (Finset.mem_insert_self _ _)).2
  · rw [← hc]
    change psiAverage ρ ψ R
      (∑ nv ∈ c.support, c nv • ((twistedRepresentation ρ ψ) nv.1 nv.2 - nv.2)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro nv hnv
    rw [map_smul]
    have hk := hkill (f nv) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨nv, hnv, rfl⟩))
    have he : ρ (Multiplicative.ofAdd (f nv).1) (f nv).2 -
        (ψ (Multiplicative.ofAdd (f nv).1) : ℂ) • (f nv).2 =
        (twistedRepresentation ρ ψ) nv.1 nv.2 - nv.2 := by
      simp [f, twistedRepresentation, smul_smul, Units.ne_zero]
    rw [he] at hk
    simp [hk]

theorem exact (ρU : Representation ℂ (Multiplicative K) U)
    (ρV : Representation ℂ (Multiplicative K) V)
    (ρW : Representation ℂ (Multiplicative K) W)
    (hU : IsSmooth ρU) (hV : IsSmooth ρV) (hW : IsSmooth ρW)
    (ψ : Multiplicative K →* ℂˣ)
    (hψc : Continuous ψ) (hψs : IsLocallyConstant ψ)
    (i : Representation.IntertwiningMap ρU ρV)
    (p : Representation.IntertwiningMap ρV ρW)
    (hi : Function.Injective i)
    (hp : Function.Surjective p)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    Function.Injective (map ρU ρV ψ i) ∧
      LinearMap.range (map ρU ρV ψ i) = LinearMap.ker (map ρV ρW ψ p) ∧
      Function.Surjective (map ρV ρW ψ p) := by
  refine ⟨?_, ?_, ?_⟩
  · change Function.Injective (Representation.Coinvariants.map
      (twistedRepresentation ρU ψ) (twistedRepresentation ρV ψ) _)
    apply TransversalAverages.coinvariants_map_injective_of_annihilating_averages
      (twistedRepresentation ρU ψ) (twistedRepresentation ρV ψ) _ hi
    intro v hv
    obtain ⟨J, L, R, hJo, hJc, hLo, hLc, hJL, hR, hRne, hψJ, hfix, hkill⟩ :=
      killsRelation ρV hV ψ hψc hψs v hv
    refine ⟨R, hRne, ?_⟩
    change psiAverage ρV ψ R v = 0
    exact hkill
  · apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
        (twistedRepresentation ρU ψ) u
      change Representation.Coinvariants.mk (twistedRepresentation ρW ψ) (p (i v)) = 0
      have hv : i v ∈ LinearMap.ker p.toLinearMap := by
        rw [← hex]
        exact LinearMap.mem_range_self _ v
      have hz : p (i v) = 0 := hv
      rw [hz, map_zero]
    · have hk : Representation.Coinvariants.ker (twistedRepresentation ρW ψ) ≤
          (Representation.Coinvariants.ker (twistedRepresentation ρV ψ)).map p.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨n, w⟩, rfl⟩
        obtain ⟨v, rfl⟩ := hp w
        refine ⟨(twistedRepresentation ρV ψ) n v - v,
          Representation.Coinvariants.sub_mem_ker n v, ?_⟩
        simp [twistedRepresentation, p.isIntertwining]
      intro u hu
      obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
        (twistedRepresentation ρV ψ) u
      have hpv : p v ∈ Representation.Coinvariants.ker (twistedRepresentation ρW ψ) :=
        (Representation.Coinvariants.mk_eq_zero _).mp hu
      obtain ⟨r, hr, hpr⟩ := hk hpv
      change p r = p v at hpr
      have hvr : v - r ∈ LinearMap.range i.toLinearMap := by
        rw [hex]
        change p (v - r) = 0
        simp [hpr]
      obtain ⟨t, ht⟩ := hvr
      refine ⟨Representation.Coinvariants.mk (twistedRepresentation ρU ψ) t, ?_⟩
      change Representation.Coinvariants.mk (twistedRepresentation ρV ψ) (i t) =
        Representation.Coinvariants.mk (twistedRepresentation ρV ψ) v
      apply (Representation.Coinvariants.mk_eq_iff _).mpr
      change i t = v - r at ht
      rw [ht]
      convert (Representation.Coinvariants.ker (twistedRepresentation ρV ψ)).neg_mem hr using 1 <;> abel
  · intro w
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective
      (twistedRepresentation ρW ψ) w
    obtain ⟨u, rfl⟩ := hp v
    exact ⟨Representation.Coinvariants.mk (twistedRepresentation ρV ψ) u, rfl⟩

variable {G : Type*} [Group G]

theorem restrict_smooth {G : Type*} [Group G] [TopologicalSpace G]
    (ρ : Representation ℂ G V)
    (hρ : ∀ v, IsOpen {g : G | ρ g v = v})
    (n : Multiplicative K →* G) (hn : Continuous n) :
    IsSmooth (ρ.comp n) := by
  intro v
  exact (hρ v).preimage (hn.comp continuous_ofAdd)

end DedekindZetaZeroFree.KPCoinvariants

end
