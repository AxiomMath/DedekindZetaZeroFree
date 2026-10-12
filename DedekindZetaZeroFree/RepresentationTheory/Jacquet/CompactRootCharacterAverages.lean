module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.SubmodulesAndQuotients
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ContinuousTwistedRootCoinvariants
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.LocalCoinvariantExactness

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPRootAverage

section AdditiveRoot

variable {K V : Type*} [AddCommGroup K] [TopologicalSpace K]
    [IsTopologicalAddGroup K] [AddCommGroup V] [Module ℂ V]

abbrev LevelQuotient (L J : AddSubgroup K) := L ⧸ J.addSubgroupOf L

theorem finite_levelQuotient (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K)) :
    Finite (LevelQuotient L J) := by
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hLcompact
  exact (J.addSubgroupOf L).quotient_finite_of_isOpen
    (hJopen.preimage continuous_subtype_val)

def representative (L J : AddSubgroup K) (q : LevelQuotient L J) : L :=
  Quotient.out q

theorem representative_mk (L J : AddSubgroup K) (q : LevelQuotient L J) :
    QuotientAddGroup.mk' (J.addSubgroupOf L) (representative L J q) = q := by
  exact Quotient.out_eq q

theorem fixedSubmodule_stable (ρ : Representation ℂ (Multiplicative K) V)
    (J : AddSubgroup K) (t : Multiplicative K) :
    fixedSubmodule ρ J.toSubgroup ≤ (fixedSubmodule ρ J.toSubgroup).comap (ρ t) := by
  intro v hv j
  change ρ (j : Multiplicative K) (ρ t v) = ρ t v
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
    hv j]

def fixedRepresentation (ρ : Representation ℂ (Multiplicative K) V)
    (J : AddSubgroup K) :
    Representation ℂ (Multiplicative K) (fixedSubmodule ρ J.toSubgroup) :=
  ρ.subrepresentation (fixedSubmodule ρ J.toSubgroup) (fixedSubmodule_stable ρ J)

theorem fixedRepresentation_eq (ρ : Representation ℂ (Multiplicative K) V)
    (L J : AddSubgroup K) {a b : L}
    (h : QuotientAddGroup.mk' (J.addSubgroupOf L) a =
      QuotientAddGroup.mk' (J.addSubgroupOf L) b) :
    fixedRepresentation ρ J (Multiplicative.ofAdd (a : K)) =
      fixedRepresentation ρ J (Multiplicative.ofAdd (b : K)) := by
  have hab' : a - b ∈ J.addSubgroupOf L := QuotientAddGroup.eq_iff_sub_mem.mp h
  have hab : (a : K) - (b : K) ∈ J := hab'
  ext v
  change ρ (Multiplicative.ofAdd (a : K)) (v : V) =
    ρ (Multiplicative.ofAdd (b : K)) (v : V)
  have hv := v.property ⟨Multiplicative.ofAdd ((a : K) - (b : K)), hab⟩
  have heq : Multiplicative.ofAdd (a : K) =
      Multiplicative.ofAdd (b : K) * Multiplicative.ofAdd ((a : K) - (b : K)) := by
    change (a : K) = (b : K) + ((a : K) - (b : K))
    abel
  rw [heq, map_mul, Module.End.mul_apply, hv]

def quotientRepresentation (ρ : Representation ℂ (Multiplicative K) V)
    (L J : AddSubgroup K) :
    Representation ℂ (Multiplicative (LevelQuotient L J))
      (fixedSubmodule ρ J.toSubgroup) where
  toFun q := fixedRepresentation ρ J
    (Multiplicative.ofAdd (representative L J (Multiplicative.toAdd q) : K))
  map_one' := by
    have h : QuotientAddGroup.mk' (J.addSubgroupOf L) (representative L J 0) =
        QuotientAddGroup.mk' (J.addSubgroupOf L) 0 := by
      rw [representative_mk]; rfl
    simpa using fixedRepresentation_eq ρ L J h
  map_mul' := by
    intro a b
    have h : QuotientAddGroup.mk' (J.addSubgroupOf L)
        (representative L J (Multiplicative.toAdd (a * b))) =
        QuotientAddGroup.mk' (J.addSubgroupOf L)
          (representative L J (Multiplicative.toAdd a) +
            representative L J (Multiplicative.toAdd b)) := by
      rw [representative_mk, map_add, representative_mk, representative_mk]
      rfl
    simpa [map_mul] using fixedRepresentation_eq ρ L J h

omit [TopologicalSpace K] [IsTopologicalAddGroup K] in
theorem character_eq (ψ : Multiplicative K →* ℂˣ)
    (L J : AddSubgroup K) (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1)
    {a b : L} (h : QuotientAddGroup.mk' (J.addSubgroupOf L) a =
      QuotientAddGroup.mk' (J.addSubgroupOf L) b) :
    ψ (Multiplicative.ofAdd (a : K)) = ψ (Multiplicative.ofAdd (b : K)) := by
  have hab' : a - b ∈ J.addSubgroupOf L := QuotientAddGroup.eq_iff_sub_mem.mp h
  have hab : (a : K) - (b : K) ∈ J := hab'
  have heq : Multiplicative.ofAdd (a : K) =
      Multiplicative.ofAdd (b : K) * Multiplicative.ofAdd ((a : K) - (b : K)) := by
    change (a : K) = (b : K) + ((a : K) - (b : K))
    abel
  rw [heq, map_mul, hψJ _ hab, mul_one]

def quotientCharacter (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K)
    (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) :
    Multiplicative (LevelQuotient L J) →* ℂˣ where
  toFun q := ψ (Multiplicative.ofAdd
    (representative L J (Multiplicative.toAdd q) : K))
  map_one' := by
    have h : QuotientAddGroup.mk' (J.addSubgroupOf L) (representative L J 0) =
        QuotientAddGroup.mk' (J.addSubgroupOf L) 0 := by
      simp [representative, QuotientAddGroup.mk'_apply, Quotient.out_eq]
    simpa using character_eq ψ L J hψJ h
  map_mul' := by
    intro a b
    have h : QuotientAddGroup.mk' (J.addSubgroupOf L)
        (representative L J (Multiplicative.toAdd (a * b))) =
        QuotientAddGroup.mk' (J.addSubgroupOf L)
          (representative L J (Multiplicative.toAdd a) +
            representative L J (Multiplicative.toAdd b)) := by
      simp only [map_add, representative, QuotientAddGroup.mk'_apply, Quotient.out_eq]
      rfl
    simpa [map_mul] using character_eq ψ L J hψJ h

theorem quotientCharacter_mk (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K)
    (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) (t : L) :
    quotientCharacter ψ L J hψJ
        (Multiplicative.ofAdd (QuotientAddGroup.mk' (J.addSubgroupOf L) t)) =
      ψ (Multiplicative.ofAdd (t : K)) := by
  exact character_eq ψ L J hψJ (representative_mk L J _)

end AdditiveRoot

end DedekindZetaZeroFree.KPRootAverage

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPRootAverage

section AdditiveRoot

variable {K V : Type*} [AddCommGroup K] [TopologicalSpace K]
    [IsTopologicalAddGroup K] [AddCommGroup V] [Module ℂ V]

theorem quotientRepresentation_mk (ρ : Representation ℂ (Multiplicative K) V)
    (L J : AddSubgroup K) (t : L) (v : fixedSubmodule ρ J.toSubgroup) :
    quotientRepresentation ρ L J
        (Multiplicative.ofAdd (QuotientAddGroup.mk' (J.addSubgroupOf L) t)) v =
      fixedRepresentation ρ J (Multiplicative.ofAdd (t : K)) v := by
  have h : QuotientAddGroup.mk' (J.addSubgroupOf L)
      (representative L J (QuotientAddGroup.mk' (J.addSubgroupOf L) t)) =
      QuotientAddGroup.mk' (J.addSubgroupOf L) t := representative_mk L J _
  exact LinearMap.congr_fun (fixedRepresentation_eq ρ L J h) v

omit [TopologicalSpace K] [IsTopologicalAddGroup K] in

def averageWithRepresentatives (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K))
    (s : LevelQuotient L J → L) :
    (fixedSubmodule ρ J.toSubgroup) →ₗ[ℂ] (fixedSubmodule ρ J.toSubgroup) :=
  letI : Finite (LevelQuotient L J) := finite_levelQuotient L J hJL hLcompact hJopen
  letI := Fintype.ofFinite (LevelQuotient L J)
  (Fintype.card (LevelQuotient L J) : ℂ)⁻¹ •
    ∑ q : LevelQuotient L J,
      (ψ (Multiplicative.ofAdd (s q : K)) : ℂ)⁻¹ •
        fixedRepresentation ρ J (Multiplicative.ofAdd (s q : K))

def characterAverage (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K)) :
    (fixedSubmodule ρ J.toSubgroup) →ₗ[ℂ] (fixedSubmodule ρ J.toSubgroup) :=
  averageWithRepresentatives ρ ψ L J hJL hLcompact hJopen (representative L J)

def eigenspace (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L : AddSubgroup K) : Submodule ℂ V where
  carrier := {v | ∀ t ∈ L, ρ (Multiplicative.ofAdd t) v =
    (ψ (Multiplicative.ofAdd t) : ℂ) • v}
  zero_mem' := by intro t ht; simp
  add_mem' := by intro v w hv hw t ht; simp [hv t ht, hw t ht, smul_add]
  smul_mem' := by
    intro a v hv t ht
    rw [map_smul, hv t ht, smul_comm]

private theorem characterAverage_isProj (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K))
    (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) :
    LinearMap.IsProj ((eigenspace ρ ψ L).comap (fixedSubmodule ρ J.toSubgroup).subtype)
      (characterAverage ρ ψ L J hJL hLcompact hJopen) := by
  classical
  letI : Finite (LevelQuotient L J) := finite_levelQuotient L J hJL hLcompact hJopen
  letI := Fintype.ofFinite (LevelQuotient L J)
  letI := Fintype.ofFinite (Multiplicative (LevelQuotient L J))
  letI : Invertible (Fintype.card (Multiplicative (LevelQuotient L J)) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  let τ := rootTwistedRepresentation (quotientRepresentation ρ L J)
    (MonoidHom.id _) (quotientCharacter ψ L J hψJ)
  have heq : characterAverage ρ ψ L J hJL hLcompact hJopen = τ.averageMap := by
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      MonoidAlgebra.of_apply, Representation.asAlgebraHom_single, one_smul,
      invOf_eq_inv]
    unfold characterAverage averageWithRepresentatives
    simp only [τ, rootTwistedRepresentation, MonoidHom.id_apply, Units.val_inv_eq_inv_val]
    rw [Fintype.card_congr (Multiplicative.ofAdd : LevelQuotient L J ≃
      Multiplicative (LevelQuotient L J))]
    congr 1
  have hinv : τ.invariants =
      (eigenspace ρ ψ L).comap (fixedSubmodule ρ J.toSubgroup).subtype := by
    ext v
    constructor
    · intro hv t ht
      have h := hv (Multiplicative.ofAdd (QuotientAddGroup.mk' (J.addSubgroupOf L) ⟨t, ht⟩))
      dsimp only [τ, rootTwistedRepresentation_apply] at h
      simp only [Units.val_inv_eq_inv_val, MonoidHom.id_apply] at h
      change ((quotientCharacter ψ L J hψJ _ : ℂ)⁻¹) •
        quotientRepresentation ρ L J _ v = v at h
      rw [quotientRepresentation_mk, quotientCharacter_mk] at h
      have hh := congrArg (fun w : fixedSubmodule ρ J.toSubgroup =>
        (ψ (Multiplicative.ofAdd t) : ℂ) • (w : V)) h
      simpa [fixedRepresentation, smul_smul] using hh
    · intro hv g
      dsimp only [τ, rootTwistedRepresentation_apply]
      simp only [Units.val_inv_eq_inv_val, MonoidHom.id_apply]
      change ((quotientCharacter ψ L J hψJ g : ℂ)⁻¹) •
        quotientRepresentation ρ L J g v = v
      apply Subtype.ext
      change (ψ (Multiplicative.ofAdd (representative L J (Multiplicative.toAdd g) : K)) : ℂ)⁻¹ •
        ρ (Multiplicative.ofAdd (representative L J (Multiplicative.toAdd g) : K)) (v : V) = v
      have hh : ρ (Multiplicative.ofAdd (representative L J (Multiplicative.toAdd g) : K)) (v : V) =
          (ψ (Multiplicative.ofAdd (representative L J (Multiplicative.toAdd g) : K)) : ℂ) • (v : V) :=
        hv _ (representative L J (Multiplicative.toAdd g)).property
      rw [hh]
      simp
  rw [heq, ← hinv]
  exact τ.isProj_averageMap

theorem characterAverage_range (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K))
    (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1) :
    LinearMap.range ((fixedSubmodule ρ J.toSubgroup).subtype.comp
        (characterAverage ρ ψ L J hJL hLcompact hJopen)) = eigenspace ρ ψ L := by
  have hp := characterAverage_isProj ρ ψ L J hJL hLcompact hJopen hψJ
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact hp.map_mem w
  · intro hv
    have hvJ : v ∈ fixedSubmodule ρ J.toSubgroup := by
      intro j
      have h := hv (Multiplicative.toAdd (j : Multiplicative K)) (hJL j.property)
      have hψ : ψ (j : Multiplicative K) = 1 := hψJ _ j.property
      simpa [hψ] using h
    refine ⟨⟨v, hvJ⟩, ?_⟩
    change (characterAverage ρ ψ L J hJL hLcompact hJopen ⟨v, hvJ⟩ : V) = v
    exact congrArg Subtype.val (hp.map_id ⟨v, hvJ⟩ hv)

private def ambientAverage (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K)) : V →ₗ[ℂ] V :=
  letI : Finite (LevelQuotient L J) := finite_levelQuotient L J hJL hLcompact hJopen
  letI := Fintype.ofFinite (LevelQuotient L J)
  (Fintype.card (LevelQuotient L J) : ℂ)⁻¹ • ∑ x : LevelQuotient L J,
    (ψ (Multiplicative.ofAdd (representative L J x : K)) : ℂ)⁻¹ •
      ρ (Multiplicative.ofAdd (representative L J x : K))

private theorem ambientAverage_apply (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K))
    (v : fixedSubmodule ρ J.toSubgroup) :
    (characterAverage ρ ψ L J hJL hLcompact hJopen v : V) =
      ambientAverage ρ ψ L J hJL hLcompact hJopen (v : V) := by
  classical
  simp [characterAverage, averageWithRepresentatives, ambientAverage, fixedRepresentation]

private theorem ambientAverage_eigen (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J : AddSubgroup K) (hJL : J ≤ L)
    (hLcompact : IsCompact (L : Set K)) (hJopen : IsOpen (J : Set K))
    (v : V) (hv : v ∈ eigenspace ρ ψ L) :
    ambientAverage ρ ψ L J hJL hLcompact hJopen v = v := by
  classical
  letI : Finite (LevelQuotient L J) := finite_levelQuotient L J hJL hLcompact hJopen
  letI := Fintype.ofFinite (LevelQuotient L J)
  have heq (x : LevelQuotient L J) :
      (ψ (Multiplicative.ofAdd (representative L J x : K)) : ℂ)⁻¹ •
        ρ (Multiplicative.ofAdd (representative L J x : K)) v = v := by
    rw [hv _ (representative L J x).property]
    simp
  simp only [ambientAverage, LinearMap.smul_apply, LinearMap.sum_apply, heq, Finset.sum_const]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp

private theorem ambientAverage_commute (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J J' : AddSubgroup K)
    (hJL : J ≤ L) (hJ'L : J' ≤ L) (hLcompact : IsCompact (L : Set K))
    (hJopen : IsOpen (J : Set K)) (hJ'open : IsOpen (J' : Set K)) :
    Commute (ambientAverage ρ ψ L J hJL hLcompact hJopen)
      (ambientAverage ρ ψ L J' hJ'L hLcompact hJ'open) := by
  classical
  letI : Finite (LevelQuotient L J) := finite_levelQuotient L J hJL hLcompact hJopen
  letI := Fintype.ofFinite (LevelQuotient L J)
  letI : Finite (LevelQuotient L J') := finite_levelQuotient L J' hJ'L hLcompact hJ'open
  letI := Fintype.ofFinite (LevelQuotient L J')
  unfold ambientAverage
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_right
  intro j hj
  apply Commute.smul_right
  apply Commute.symm
  apply Commute.sum_right
  intro i hi
  apply Commute.smul_right
  exact (Commute.all (Multiplicative.ofAdd (representative L J' j : K))
    (Multiplicative.ofAdd (representative L J i : K))).map ρ

theorem characterAverage_refinement (ρ : Representation ℂ (Multiplicative K) V)
    (ψ : Multiplicative K →* ℂˣ) (L J J' : AddSubgroup K)
    (hJL : J ≤ L) (hJ'L : J' ≤ L) (hJ'J : J' ≤ J)
    (hLcompact : IsCompact (L : Set K))
    (hJopen : IsOpen (J : Set K)) (hJ'open : IsOpen (J' : Set K))
    (hψJ : ∀ j ∈ J, ψ (Multiplicative.ofAdd j) = 1)
    (v : V) (hv : v ∈ fixedSubmodule ρ J.toSubgroup)
    (hv' : v ∈ fixedSubmodule ρ J'.toSubgroup) :
    (characterAverage ρ ψ L J hJL hLcompact hJopen ⟨v, hv⟩ : V) =
      (characterAverage ρ ψ L J' hJ'L hLcompact hJ'open ⟨v, hv'⟩ : V) := by
  let A := ambientAverage ρ ψ L J hJL hLcompact hJopen
  let B := ambientAverage ρ ψ L J' hJ'L hLcompact hJ'open
  have hA : A v ∈ eigenspace ρ ψ L := by
    rw [← ambientAverage_apply ρ ψ L J hJL hLcompact hJopen ⟨v, hv⟩]
    exact (characterAverage_isProj ρ ψ L J hJL hLcompact hJopen hψJ).map_mem ⟨v, hv⟩
  have hB : B v ∈ eigenspace ρ ψ L := by
    rw [← ambientAverage_apply ρ ψ L J' hJ'L hLcompact hJ'open ⟨v, hv'⟩]
    exact (characterAverage_isProj ρ ψ L J' hJ'L hLcompact hJ'open
      (fun j hj => hψJ j (hJ'J hj))).map_mem ⟨v, hv'⟩
  have hc := LinearMap.congr_fun
    (ambientAverage_commute ρ ψ L J J' hJL hJ'L hLcompact hJopen hJ'open).eq v
  change A (B v) = B (A v) at hc
  rw [ambientAverage_apply ρ ψ L J hJL hLcompact hJopen ⟨v, hv⟩,
    ambientAverage_apply ρ ψ L J' hJ'L hLcompact hJ'open ⟨v, hv'⟩]
  calc A v = B (A v) := (ambientAverage_eigen ρ ψ L J' hJ'L hLcompact hJ'open (A v) hA).symm
    _ = A (B v) := hc.symm
    _ = B v := ambientAverage_eigen ρ ψ L J hJL hLcompact hJopen (B v) hB

end AdditiveRoot

end DedekindZetaZeroFree.KPRootAverage

end
end
