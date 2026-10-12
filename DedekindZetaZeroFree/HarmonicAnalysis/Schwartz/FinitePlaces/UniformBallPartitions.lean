module

public import DedekindZetaZeroFree.Arithmetic.Ideals.GlobalValuationBounds
public import DedekindZetaZeroFree.Adeles.Approximation.SIntegerFiniteStrongApproximation

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Filter
open scoped Classical nonZeroDivisors

namespace DedekindZetaZeroFree.PoissonSUniformBallPartition

def coset (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) (t : F) :
    Set (PoissonFinite.Space F S) :=
  {z | z - PoissonFinite.diagonal F S t ∈ PoissonS.finiteBall F S k}

theorem finiteBall_eq_valuation_product (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) :
    PoissonS.finiteBall F S k =
      {z | ∀ v : S, z v ∈ PoissonSLocalBalls.ball F v.val (k v)} := by
  ext z
  simp only [PoissonS.finiteBall, Set.mem_setOf_eq]
  apply forall_congr'
  intro v
  exact (Set.ext_iff.mp (PoissonSLocalBalls.ball_eq_normBall F v.val (k v)) (z v)).symm

private theorem ideal_fiber (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) :
    (↑(PoissonS.ballFractionalIdeal F S k) : Set F) =
      {i : F | i ∈ sIntegerRing F S ∧
        PoissonFinite.diagonal F S i ∈ PoissonS.finiteBall F S k} := by
  rw [← sGlobalBoundedIdealSet_eq_ballFractionalIdeal]
  ext i
  rw [finiteBall_eq_valuation_product]
  simp only [sGlobalBoundedIdealSet, Set.mem_setOf_eq,
    PoissonSLocalBalls.mem_ball, PoissonFinite.diagonal,
    HeightOneSpectrum.adicCompletion.valued_coe]
  have hv (v : S) : Valued.v (FinitePlace.embedding v.val i) = v.val.valuation F i :=
    HeightOneSpectrum.adicCompletion.valued_coe _ _ _
  simp_rw [hv]

theorem exists_uniform_ball_partition (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v : S, IsLocallyConstant (φ v))
    (hsupport : ∀ v : S, HasCompactSupport (φ v)) :
    ∃ (k : S → ℤ) (n : ℕ) (t : Fin n → sIntegerRing F S) (c : Fin n → ℂ),
      Pairwise (fun j l : Fin n =>
        Disjoint (coset F S k (t j : F)) (coset F S k (t l : F))) ∧
      (∀ z : PoissonFinite.Space F S,
        (∏ v : S, φ v (z v)) =
          ∑ j : Fin n, c j *
            (coset F S k (t j : F)).indicator (fun _ => (1 : ℂ)) z) ∧
      PoissonS.ballFractionalIdeal F S k ≠ 0 ∧
      (↑(PoissonS.ballFractionalIdeal F S k) : Set F) ⊆ sIntegerRing F S ∧
      (↑(PoissonS.ballFractionalIdeal F S k) : Set F) =
        {i : F | i ∈ sIntegerRing F S ∧
          PoissonFinite.diagonal F S i ∈ PoissonS.finiteBall F S k} ∧
      (∀ j : Fin n,
        {m : F | m ∈ sIntegerRing F S ∧
          PoissonFinite.diagonal F S m ∈ coset F S k (t j : F)} =
        (fun i : F => (t j : F) + i) ''
          (↑(PoissonS.ballFractionalIdeal F S k) : Set F)) := by
  let ψ : PoissonFinite.Space F S → ℂ := fun x => ∏ v : S, φ v (x v)
  have hl : IsLocallyConstant ψ := by
    apply (IsLocallyConstant.iff_eventually_eq ψ).2
    intro x
    have h : ∀ v : S, ∀ᶠ y in nhds x, φ v (y v) = φ v (x v) := by
      intro v
      exact ((hlocal v).comp_continuous (continuous_apply v)).eventually_eq x
    filter_upwards [Filter.eventually_all.mpr h] with y hy
    exact Finset.prod_congr rfl (fun v _ => hy v)
  have hc : HasCompactSupport ψ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_pi_infinite (fun v : S => (hsupport v).isCompact))
    intro x hx v
    apply subset_tsupport
    exact (Finset.prod_ne_zero_iff.mp hx) v (Finset.mem_univ v)
  obtain ⟨k, n, b, c, hexp⟩ :=
    PoissonFinite.BallExpansion.exists_uniform_ball_expansion F S ψ hl hc
  let U : AddSubgroup (PoissonFinite.Space F S) :=
    AddSubgroup.pi Set.univ (fun v => PoissonSLocalBalls.ball F v.val (k v))
  let q := QuotientAddGroup.mk' U
  have hq (x y : PoissonFinite.Space F S) : q x = q y ↔
      ∀ v : S, Valued.v (x v - y v) ≤ WithZero.exp (-k v) := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_iff_sub_mem]
    simp [U, AddSubgroup.mem_pi, PoissonSLocalBalls.mem_ball]
  have hψ (x y : PoissonFinite.Space F S) (h : q x = q y) : ψ x = ψ y := by
    rw [hexp x, hexp y]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∀ v : S, Valued.v (x v - b j v) ≤ WithZero.exp (-k v)) ↔
        (∀ v : S, Valued.v (y v - b j v) ≤ WithZero.exp (-k v)) := by
      rw [← hq, ← hq, h]
    simp only [he]
  let T := Finset.univ.image (fun j : Fin n => q (b j))
  have hmem (x : PoissonFinite.Space F S) (hx : ψ x ≠ 0) : q x ∈ T := by
    rw [hexp x] at hx
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have hj' : ∀ v : S, Valued.v (x v - b j v) ≤ WithZero.exp (-k v) := by
      by_contra hn
      rw [if_neg hn, mul_zero] at hj
      exact hj rfl
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ((hq x (b j)).mpr hj').symm⟩
  have hlift (j : T) : ∃ t : sIntegerRing F S,
      q (PoissonFinite.diagonal F S (t : F)) = j.val := by
    obtain ⟨t, ht⟩ := PoissonSFiniteDensity.local_congruence_approximation F S k j.val.out
    refine ⟨t, ?_⟩
    have he : q (PoissonFinite.diagonal F S (t : F)) = q j.val.out :=
      (hq _ _).mpr ht
    exact he.trans (Quotient.out_eq j.val)
  choose t ht using hlift
  have hcos (x : PoissonFinite.Space F S) (j : T) :
      x ∈ coset F S k (t j : F) ↔ q x = j.val := by
    rw [coset, Set.mem_setOf_eq, finiteBall_eq_valuation_product]
    change (∀ v : S, Valued.v (x v - PoissonFinite.diagonal F S (t j : F) v) ≤
      WithZero.exp (-k v)) ↔ _
    rw [← hq, ht]
  have hsum (x : PoissonFinite.Space F S) :
      ψ x = ∑ j : T, ψ (PoissonFinite.diagonal F S (t j : F)) *
        (coset F S k (t j : F)).indicator (fun _ => (1 : ℂ)) x := by
    simp_rw [Set.indicator_apply, hcos]
    by_cases hx : q x ∈ T
    · let j : T := ⟨q x, hx⟩
      rw [Finset.sum_eq_single j]
      · change ψ x = ψ (PoissonFinite.diagonal F S (t j : F)) *
          (if q x = j.val then (1 : ℂ) else 0)
        rw [if_pos rfl, mul_one]
        exact hψ x _ (ht j).symm
      · intro l _ hlj
        have hne : q x ≠ l.val := by
          intro he
          exact hlj (Subtype.ext he.symm)
        simp [hne]
      · simp
    · have hz : ψ x = 0 := by
        by_contra hn
        exact hx (hmem x hn)
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have hn : q x ≠ j.val := fun he => hx (he.symm ▸ j.property)
      simp [hn]
  let e := (Fintype.equivFin T).symm
  refine ⟨k, Fintype.card T, fun j => t (e j),
    fun j => ψ (PoissonFinite.diagonal F S (t (e j) : F)), ?_, ?_,
    PoissonS.ballFractionalIdeal_ne_zero F S k, ?_, ideal_fiber F S k, ?_⟩
  · intro j l hjl
    apply Set.disjoint_left.mpr
    intro x hxj hxl
    have he : (e j).val = (e l).val := ((hcos x (e j)).mp hxj).symm.trans
      ((hcos x (e l)).mp hxl)
    exact hjl (e.injective (Subtype.ext he))
  · intro z
    change ψ z = ∑ j, ψ (PoissonFinite.diagonal F S (t (e j) : F)) *
      (coset F S k (t (e j) : F)).indicator (fun _ => (1 : ℂ)) z
    rw [hsum z]
    exact (Equiv.sum_comp e _).symm
  · rw [ideal_fiber F S k]
    exact fun _ hx => hx.1
  · intro j
    ext m
    constructor
    · rintro ⟨hm, hb⟩
      refine ⟨m - (t (e j) : F), ?_, by simp⟩
      rw [ideal_fiber F S k]
      refine ⟨(sIntegerRing F S).sub_mem hm (t (e j)).property, ?_⟩
      have hd : PoissonFinite.diagonal F S (m - (t (e j) : F)) =
          PoissonFinite.diagonal F S m - PoissonFinite.diagonal F S (t (e j) : F) := by
        ext v
        simpa only [PoissonFinite.diagonal, Pi.sub_apply] using
          congrArg (fun x : v.val.adicCompletion F => x.toCompletion)
            (map_sub (FinitePlace.embedding (K := F) v.val) m (t (e j) : F))
      rw [hd]
      exact hb
    · rintro ⟨i, hi, rfl⟩
      rw [ideal_fiber F S k] at hi
      refine ⟨(sIntegerRing F S).add_mem (t (e j)).property hi.1, ?_⟩
      change PoissonFinite.diagonal F S ((t (e j) : F) + i) -
        PoissonFinite.diagonal F S (t (e j) : F) ∈ PoissonS.finiteBall F S k
      have hd : PoissonFinite.diagonal F S ((t (e j) : F) + i) -
          PoissonFinite.diagonal F S (t (e j) : F) = PoissonFinite.diagonal F S i := by
        ext v
        simp [PoissonFinite.diagonal, map_add]
      rw [hd]
      exact hi.2

end DedekindZetaZeroFree.PoissonSUniformBallPartition

end
