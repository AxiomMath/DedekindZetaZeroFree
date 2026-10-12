module

public import DedekindZetaZeroFree.Metaplectic.Weil.Finite.PerfectQuadraticQuotients
public import DedekindZetaZeroFree.Metaplectic.Weil.LocalQuadraticCosetIntegrals

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

 local instance cutoffCosetCompletionMeasurable
    (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

 local instance cutoffCosetCompletionBorel
    (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def localFiniteStationaryGaussSum
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ)
    (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) : ℂ :=
  let G := localScaledBallDualQuotient F v b m
  letI : Finite G := finite_localScaledBallDualQuotient F v b m hHL
  letI : Fintype G := Fintype.ofFinite G
  ((localNormalizedHaar F v
      (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal : ℂ) *
    ∑ g : G, (localFinitePerfectQuadraticPhase F v a b hb m hq hHL g : ℂ)

theorem weil_finite_cutoff_coset_reduction
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ)
    (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m)
    (U : AddSubgroup (v.adicCompletion F))
    (hUc : IsCompact (U : Set (v.adicCompletion F)))
    (hUo : IsOpen (U : Set (v.adicCompletion F)))
    (hLU : localScaledBallDual F v b m ≤ U) :
    (∫ x in (U : Set (v.adicCompletion F)),
      (localFiniteCharacter F v ((a : v.adicCompletion F) * x ^ 2) : ℂ)
        ∂(localNormalizedHaar F v)) =
      localFiniteStationaryGaussSum F v a b hb m hq hHL := by
  let H := finiteCompletionBall F v m
  let L := localScaledBallDual F v b m
  let μ := localNormalizedHaar F v
  let f : v.adicCompletion F → ℂ := fun x =>
    (localFiniteCharacter F v ((a : v.adicCompletion F) * x ^ 2) : ℂ)
  have hHU : H ≤ U := hHL.trans hLU
  let Q := U ⧸ H.comap U.subtype
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  letI : Finite Q := AddSubgroup.quotient_finite_of_isOpen _
    ((isOpen_finiteCompletionBall F v m).preimage continuous_subtype_val)
  letI : Fintype Q := Fintype.ofFinite Q
  let r : Q → U := Quotient.out
  let C : Q → Set (v.adicCompletion F) := fun i => {x | x - r i ∈ H}
  have hr (i : Q) : QuotientAddGroup.mk (r i) = i := Quotient.out_eq _
  have hdis : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hs : (r i : v.adicCompletion F) - r j ∈ H := by
      convert H.sub_mem hj hi using 1 <;> abel
    have he : (QuotientAddGroup.mk (r i) : Q) =
        QuotientAddGroup.mk (r j) := QuotientAddGroup.eq_iff_sub_mem.mpr hs
    rw [hr, hr] at he
    exact hij he
  have hunion : (U : Set (v.adicCompletion F)) = ⋃ i, C i := by
    ext x
    constructor
    · intro hx
      let y : U := ⟨x, hx⟩
      let i : Q := QuotientAddGroup.mk y
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have he : (QuotientAddGroup.mk y : Q) = QuotientAddGroup.mk (r i) := (hr i).symm
      exact QuotientAddGroup.eq_iff_sub_mem.mp he
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have := U.add_mem (hHU hi) (r i).property
      simpa only [sub_add_cancel, SetLike.mem_coe] using this
  have hmeas (i : Q) : MeasurableSet (C i) :=
    (isOpen_finiteCompletionBall_coset F v (r i) m).measurableSet
  have hint (i : Q) : IntegrableOn f (C i) μ := by
    simpa only [zero_mul, sub_zero, f, C, H, μ] using
      (localQuadraticPhase_coset_integral F v a m hq (r i) 0).1
  have heval (i : Q) : (∫ x in C i, f x ∂μ) =
      if (r i : v.adicCompletion F) ∈ L then
        ((μ (H : Set (v.adicCompletion F))).toReal : ℂ) * f (r i) else 0 := by
    simpa only [zero_mul, sub_zero, ← hb, ← mem_localScaledBallDual, f, C, H, L, μ] using
      (localQuadraticPhase_coset_integral F v a m hq (r i) 0).2
  have hLmeas : MeasurableSet (L : Set (v.adicCompletion F)) :=
    (localScaledBallDual_compact_open_fractionalIdeals F v b m).2.2.2.1.measurableSet
  have hrestrict (i : Q) : (∫ x in C i, f x ∂μ) =
      ∫ x in C i ∩ (L : Set (v.adicCompletion F)), f x ∂μ := by
    by_cases hi : (r i : v.adicCompletion F) ∈ L
    · have hsub : C i ⊆ (L : Set (v.adicCompletion F)) := by
        intro x hx
        simpa only [sub_add_cancel, SetLike.mem_coe] using L.add_mem (hHL hx) hi
      rw [Set.inter_eq_left.mpr hsub]
    · have hempty : C i ∩ (L : Set (v.adicCompletion F)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxL⟩
        apply hi
        convert L.sub_mem hxL (hHL hx) using 1 <;> abel
      rw [hempty, setIntegral_empty, heval, if_neg hi]
  have hUL : (U : Set (v.adicCompletion F)) ∩ L = L :=
    Set.inter_eq_right.mpr hLU
  have heqL : (∫ x in (U : Set (v.adicCompletion F)), f x ∂μ) =
      ∫ x in (L : Set (v.adicCompletion F)), f x ∂μ := by
    rw [hunion, integral_iUnion_fintype hmeas hdis hint]
    simp_rw [hrestrict]
    rw [← integral_iUnion_fintype
      (fun i => (hmeas i).inter hLmeas)
      (fun i j hij => (hdis hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun i => (hint i).mono_set Set.inter_subset_left)]
    rw [← Set.iUnion_inter, ← hunion, hUL]
  let G := localScaledBallDualQuotient F v b m
  letI : Finite G := finite_localScaledBallDualQuotient F v b m hHL
  letI : Fintype G := Fintype.ofFinite G
  let t : G → L := Quotient.out
  let D : G → Set (v.adicCompletion F) := fun i => {x | x - t i ∈ H}
  have ht (i : G) : QuotientAddGroup.mk (t i) = i := Quotient.out_eq _
  have hDdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hs : (t i : v.adicCompletion F) - t j ∈ H := by
      convert H.sub_mem hj hi using 1 <;> abel
    have he : (QuotientAddGroup.mk (t i) : G) =
        QuotientAddGroup.mk (t j) := QuotientAddGroup.eq_iff_sub_mem.mpr hs
    rw [ht, ht] at he
    exact hij he
  have hDunion : (L : Set (v.adicCompletion F)) = ⋃ i, D i := by
    ext x
    constructor
    · intro hx
      let y : L := ⟨x, hx⟩
      let i : G := QuotientAddGroup.mk y
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have he : (QuotientAddGroup.mk y : G) = QuotientAddGroup.mk (t i) := (ht i).symm
      exact QuotientAddGroup.eq_iff_sub_mem.mp he
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have := L.add_mem (hHL hi) (t i).property
      simpa only [sub_add_cancel, SetLike.mem_coe] using this
  change (∫ x in (U : Set (v.adicCompletion F)), f x ∂μ) = _
  rw [heqL, hDunion, integral_iUnion_fintype
    (fun i => (isOpen_finiteCompletionBall_coset F v (t i) m).measurableSet)
    hDdis (fun i => by simpa only [zero_mul, sub_zero, f, C, D, H, μ] using
      (localQuadraticPhase_coset_integral F v a m hq (t i) 0).1)]
  unfold localFiniteStationaryGaussSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hevalD := (localQuadraticPhase_coset_integral F v a m hq (t i) 0).2
  have hi : (b : v.adicCompletion F) * (t i : v.adicCompletion F) ∈
      localFiniteAnnihilator F v H := (t i).property
  have hphase : localFinitePerfectQuadraticPhase F v a b hb m hq hHL i =
      localFiniteCharacter F v ((a : v.adicCompletion F) * (t i : v.adicCompletion F) ^ 2) := by
    conv_lhs => rw [← ht i, localFinitePerfectQuadraticPhase_mk]
  rw [hphase]
  simpa only [zero_mul, sub_zero, ← hb, if_pos hi, f, μ, H] using hevalD

theorem localFiniteQuadraticCutoff_eventually_eq_stationaryGaussSum
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (b : (v.adicCompletion F)ˣ)
    (hb : (b : v.adicCompletion F) = 2 * (a : v.adicCompletion F))
    (m : ℤ)
    (hq : ∀ h ∈ finiteCompletionBall F v m,
      localFiniteCharacter F v ((a : v.adicCompletion F) * h ^ 2) = 1)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫ x in (finiteCompletionBall F v (-(n : ℤ)) : Set (v.adicCompletion F)),
        (localFiniteCharacter F v ((a : v.adicCompletion F) * x ^ 2) : ℂ)
          ∂(localNormalizedHaar F v)) =
        localFiniteStationaryGaussSum F v a b hb m hq hHL := by
  obtain ⟨N, hN⟩ := localScaledBallDual_eventually_le_expanding_ball F v b m
  refine ⟨N, fun n hn => ?_⟩
  exact weil_finite_cutoff_coset_reduction F v a b hb m hq hHL
    (finiteCompletionBall F v (-(n : ℤ)))
    (isCompact_finiteCompletionBall F v _) (isOpen_finiteCompletionBall F v _)
    (hN n hn).2

end DedekindZetaZeroFree

end
