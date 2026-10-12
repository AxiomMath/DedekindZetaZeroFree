module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section
open scoped Classical Topology
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PoissonFinite.BallExpansion

theorem exists_open_phase_annihilator
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (K : Set (((v : S) → v.val.adicCompletion F))) (hK : IsCompact K) :
    ∃ U : AddSubgroup (((v : S) → v.val.adicCompletion F)), IsOpen (U : Set (((v : S) → v.val.adicCompletion F))) ∧
      ∀ u ∈ U, ∀ x ∈ K, (∏ v : S, (e v (-x v * u v) : ℂ)) = 1 := by
  let X := (v : S) → v.val.adicCompletion F
  let q : X × X → Circle := fun p ↦ ∏ v : S, e v (-p.1 v * p.2 v)
  have hq : Continuous q := by
    apply continuous_finset_prod
    intro v hv
    exact (he v).comp (((continuous_apply v).comp continuous_fst).neg.mul
      ((continuous_apply v).comp continuous_snd))
  have hq0 (x : X) : q (x, 0) = 1 := by
    change (∏ v : S, e v (-x v * (0 : v.val.adicCompletion F))) = 1
    simp
  let T : Set (X × X) := q ⁻¹' Circle.centeredArc (Real.pi / 2)
  have hT : T ∈ (𝓝ˢ K) ×ˢ 𝓝 (0 : X) := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro x hx
    rw [← nhds_prod_eq]
    apply (hq.isOpen_preimage _ (Circle.isOpen_centeredArc _)).mem_nhds
    change q (x, 0) ∈ Circle.centeredArc (Real.pi / 2)
    rw [hq0]
    simpa using mem_of_mem_nhds
      (Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial)
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hT
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean B hB
  refine ⟨U.toAddSubgroup, U.isOpen, ?_⟩
  intro u hu x hx
  let χ : AddChar X Circle :=
    { toFun := fun u ↦ q (x, u)
      map_zero_eq_one' := hq0 x
      map_add_eq_mul' := by
        intro a b
        change (∏ v : S, e v (-x v * (a v + b v))) =
          (∏ v : S, e v (-x v * a v)) * ∏ v : S, e v (-x v * b v)
        simp only [mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib] }
  have hχ : χ u = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n hn
    rw [← χ.map_nsmul_eq_pow]
    exact hAB ⟨subset_of_mem_nhdsSet hA hx, hU (U.nsmul_mem hu n)⟩
  have hcoe := congrArg Circle.coeHom hχ
  change Circle.coeHom (∏ v : S, e v (-x v * u v)) = Circle.coeHom 1 at hcoe
  rw [map_prod, map_one] at hcoe
  exact hcoe

end DedekindZetaZeroFree.PoissonFinite.BallExpansion

end
