module

public import DedekindZetaZeroFree.Theta.Whittaker.Borel.RootFibersAndHaar

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildKernelSource

theorem rawBorelRootFiber_continuous
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (θ : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (hcont : Continuous θ)
    (hrational : ∀ (γ : KPRationalAdelicSplitting.RationalPGL2 F) g,
      θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g)
    (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    Continuous (rawBorelRootFiber F ζ hζ θ b) := by
  letI : ∀ v : KPHilbert.Place F, TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : TopologicalSpace (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.restrictedTopology F ζ hζ
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hcoord (v : KPHilbert.Place F) :
      Continuous (fun x : KPGlobalTorusFunctionData.Adeles F =>
        KPStandardLocalRootLifts.N F ζ hζ v
          (KPAdelicCoverRestrictedProduct.adeleEval F v x)) := by
    cases v with
    | inl w =>
      exact (KPStandardLocalRootLifts.complex_N_continuous F ζ hζ w).comp
        ((continuous_apply w).comp continuous_fst)
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).comp
        ((RestrictedProduct.continuous_eval q).comp continuous_snd)
  let U : Set (KPGlobalTorusFunctionData.Adeles F) :=
    {x | ∀ q, ¬ KPAdelicCoverRestrictedProduct.Bad F q →
      x.2 q ∈ q.adicCompletionIntegers F}
  have hU : IsOpen U :=
    (RestrictedProduct.isOpen_forall_imp_mem
      (fun q : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring
        (q.adicCompletion F))).preimage continuous_snd
  have h0 : (0 : KPGlobalTorusFunctionData.Adeles F) ∈ U := by
    intro q hq
    exact zero_mem _
  let S : Set (KPHilbert.Place F) :=
    {v | match v with | .inl _ => True | .inr q => ¬ KPAdelicCoverRestrictedProduct.Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨Set.toFinite _, by simpa [S] using KPAdelicCoverRestrictedProduct.bad_finite F⟩
  have hmem (x : U) (v : KPHilbert.Place F) (hv : v ∈ S) :
      KPStandardLocalRootLifts.N F ζ hζ v
        (KPAdelicCoverRestrictedProduct.adeleEval F v x) ∈
          KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q =>
      have hi (t : q.adicCompletion F) :
          t ∈ KPTameCompact.O F q ↔ t ∈ q.adicCompletionIntegers F := by
        letI : ValuativeRel (q.adicCompletion F) :=
          ClassFieldTheory.finitePlaceCompletionValuativeRel F q
        change (ValuativeRel.valuation (q.adicCompletion F)) t ≤ 1 ↔ Valued.v t ≤ 1
        rw [← Valuation.vle_one_iff]
        letI : Valued.v.Compatible := Valuation.Compatible.ofValuation
          (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))
        exact Valuation.vle_one_iff Valued.v
      have hx : x.val.2 q ∈ KPTameCompact.O F q := (hi _).mpr (x.property q hv)
      simp only [KPAdelicCoverRestrictedProduct.compact,
        KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hv]
      refine ⟨KPStandardLocalRootLifts.integralN F q ⟨_, hx⟩, ?_⟩
      exact (KPStandardLocalRootLifts.N_eq_compact F ζ hζ q
        (fun h3 => hv (Or.inr h3)) ⟨_, hx⟩).symm
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _))
      (Filter.principal S) :=
    fun x => ⟨fun v => KPStandardLocalRootLifts.N F ζ hζ v
      (KPAdelicCoverRestrictedProduct.adeleEval F v x), hmem x⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (hcoord v).comp continuous_subtype_val))
  have hrt : ContinuousAt (KPGlobalTorusFunctionData.rootTuple F ζ hζ) 0 := by
    have hr : Continuous (U.domRestrict (KPGlobalTorusFunctionData.rootTuple F ζ hζ)) :=
      (RestrictedProduct.continuous_inclusion hS).comp hf
    exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h0)
  have hN : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
    have hh : Continuous (KPGlobalTorusFunctionData.Nhom F ζ hζ) := by
      apply continuous_of_continuousAt_one
      exact QuotientGroup.continuous_mk.continuousAt.comp
        (QuotientGroup.continuous_mk.continuousAt.comp hrt)
    exact hh
  let A := NumberField.AdeleRing (𝓞 F) F
  let R := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  have hrat (s : F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
      θ (KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F A s) * g) = θ g := by
    have hn : KPGlobalTorusFunctionData.N F ζ hζ (algebraMap F A s) =
        KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
          (KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.n F s)) := by
      change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPRationalAdelicSplitting.N F ζ hζ (algebraMap F A s)) = _
      rw [KPRationalAdelicSplitting.N_rational]
      rfl
    rw [hn]
    exact hrational _ _
  have hfiber (z : A) : rawBorelRootFiber F ζ hζ θ b (QuotientAddGroup.mk z) =
      θ (KPGlobalTorusFunctionData.N F ζ hζ z * b.val) := by
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R z
    obtain ⟨s, hs⟩ := r.property
    change θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk z)) * b.val) = _
    rw [hr, ← hs, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc, hrat]
  apply (QuotientAddGroup.isQuotientMap_mk R).continuous_iff.mpr
  change Continuous (fun z : A => rawBorelRootFiber F ζ hζ θ b (QuotientAddGroup.mk z))
  simp_rw [hfiber]
  exact hcont.comp (hN.mul continuous_const)

end DedekindZetaZeroFree.KPWildKernelSource

end
