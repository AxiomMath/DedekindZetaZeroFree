module

public import DedekindZetaZeroFree.Metaplectic.Kubota.GenuineCuspLinesAndUnitaryMonodromy

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

theorem horizontal_average_continuous_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ)
    (hf : Continuous (fun x : KPCuspCharts.Cross F =>
      f (QuotientAddGroup.mk x.1) x.2))
    (hinv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      f (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        f (QuotientAddGroup.mk x.1) x.2) :
    Continuous (fun x : KPCuspCharts.Cross F => ∫ z, f z x.2 ∂μ) ∧
      (∀ (s : S) (x : KPCuspCharts.Cross F),
        (∫ z, f z (G.crossAction s x).2 ∂μ) = ∫ z, f z x.2 ∂μ) := by
  letI := hμ
  letI := hprob
  obtain ⟨hd, _⟩ := G.lattice
  letI := hd
  have hle : KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) ≤
      KPCuspCharts.translationLattice F D.L := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a, ha.1, rfl⟩
  letI : DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule :=
    DiscreteTopology.of_subset hd hle
  letI : DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)) :=
    ‹DiscreteTopology (KPCuspCharts.translationLattice F
      (KPCuspGenuineMonodromy.kernelLattice S D ρ)).toIntSubmodule›
  letI : BorelSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) := inferInstance
  have hrel : ∀ x y : KPCuspCharts.Cross F,
      KPCuspCharts.crossRelation F S x y →
        f (QuotientAddGroup.mk x.1) x.2 = f (QuotientAddGroup.mk y.1) y.2 := by
    intro x y hxy
    change MulAction.orbitRel S _ (KPCuspCharts.toArch F (x, 0))
      (KPCuspCharts.toArch F (y, 0)) at hxy
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp ((MulAction.orbitRel_apply).mp hxy)
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (y, 0)) =
      KPCuspCharts.toArch F (x, 0) at hs
    rw [G.actual_action s A hA hc] at hs
    have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective hs
    have hx : G.crossAction s y = x := by
      rw [G.crossAction_formula s A hA hc]
      exact congrArg Prod.fst hp
    rw [← hx]
    exact hinv s y
  let q : KPCuspCharts.CrossQuotient F S → ℝ :=
    Quotient.lift (fun x => f (QuotientAddGroup.mk x.1) x.2) hrel
  have hq : Continuous q := hf.quotient_lift _
  letI := G.compact_cross
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  have hbound : ∀ z b, ‖f z b‖ ≤ C := by
    intro z b
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hC (Quotient.mk _ (y, b)) (Set.mem_univ _)
  have hmeas : ∀ b, Measurable (fun z => f z b) := by
    intro b
    apply measurable_from_quotient.mpr
    exact (hf.comp (continuous_id.prodMk continuous_const)).measurable
  constructor
  · apply continuous_of_dominated (bound := fun _ => C)
    · intro x
      exact (hmeas x.2).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun z => hbound z x.2
    · exact integrable_const C
    · apply Filter.Eventually.of_forall
      intro z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
      exact (hf.comp (continuous_const.prodMk continuous_snd))
  · intro s x
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    let R : F →+* KPCuspCharts.Horizontal F :=
      { toFun := KPCuspCharts.embedding F
        map_zero' := (KPCuspCharts.embedding F).map_zero
        map_add' := (KPCuspCharts.embedding F).map_add
        map_one' := by ext i; simp [KPCuspCharts.embedding]
        map_mul' := by intro a b; ext i; simp [KPCuspCharts.embedding] }
    let M : S → KPCuspGenuineMonodromy.KernelTorus S D ρ →+
        KPCuspGenuineMonodromy.KernelTorus S D ρ := fun t =>
      QuotientAddGroup.map _ _
        (AddMonoidHom.mulLeft (R ((D.ratio t : Fˣ) : F))) (by
          intro y hy
          obtain ⟨a, ha, rfl⟩ := hy
          exact ⟨((D.ratio t : Fˣ) : F) * a,
            KPCuspGenuineMonodromy.kernelLattice_stable S D ρ t ⟨a, ha⟩,
            R.map_mul _ _⟩)
    have hMmk (t : S) (y : KPCuspCharts.Horizontal F) :
        M t (QuotientAddGroup.mk y) =
          QuotientAddGroup.mk (R ((D.ratio t : Fˣ) : F) * y) := rfl
    have hMcont (t : S) : Continuous (M t) := by
      rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
      exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)
    have hMinv (t : S) (z : KPCuspGenuineMonodromy.KernelTorus S D ρ) :
        M t⁻¹ (M t z) = z := by
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
      rw [hMmk, hMmk, ← mul_assoc, ← map_mul]
      simp
    have hMsurj (t : S) : Function.Surjective (M t) := by
      intro z
      refine ⟨M t⁻¹ z, ?_⟩
      simpa using hMinv t⁻¹ z
    letI : (Measure.map (M s) μ).IsAddHaarMeasure :=
      Measure.isAddHaarMeasure_map_of_isFiniteMeasure μ (M s) (hMcont s) (hMsurj s)
    letI : IsProbabilityMeasure (Measure.map (M s) μ) :=
      inferInstance
    have hmap : Measure.map (M s) μ = μ :=
      Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
    let c : KPCuspGenuineMonodromy.KernelTorus S D ρ :=
      QuotientAddGroup.mk (R (A 0 1 / A 1 1))
    let e : KPCuspGenuineMonodromy.KernelTorus S D ρ ≃ₜ
        KPCuspGenuineMonodromy.KernelTorus S D ρ :=
      { toFun := fun z => M s z + c
        invFun := fun z => M s⁻¹ (z - c)
        left_inv := fun z => by simp only [add_sub_cancel_right]; exact hMinv s z
        right_inv := fun z => by
          have hi : M s (M s⁻¹ (z - c)) = z - c := by
            simpa using hMinv s⁻¹ (z - c)
          change M s (M s⁻¹ (z - c)) + c = z
          rw [hi, sub_add_cancel]
        continuous_toFun := (hMcont s).add continuous_const
        continuous_invFun := (hMcont s⁻¹).comp (continuous_id.sub continuous_const) }
    have hep : MeasurePreserving e μ μ :=
      (measurePreserving_add_right μ c).comp ⟨(hMcont s).measurable, hmap⟩
    have heq : ∀ z,
        f (e z) (G.crossAction s x).2 = f z x.2 := by
      intro z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
      have hi := hinv s (y, x.2)
      rw [G.crossAction_formula s A hA hc] at hi ⊢
      change f (M s (QuotientAddGroup.mk y) + c)
        (x.2 + KPCuspLogShape.logarithm F hF D.E D.integralUnits
          (Additive.ofMul (D.ratio s))) = _
      rw [hMmk, ← QuotientAddGroup.mk_add]
      exact hi
    calc
      (∫ z, f z (G.crossAction s x).2 ∂μ) =
          ∫ z, f (e z) (G.crossAction s x).2 ∂μ :=
        (hep.integral_comp e.toMeasurableEquiv.measurableEmbedding _).symm
      _ = ∫ z, f z x.2 ∂μ := integral_congr_ae (Filter.Eventually.of_forall heq)

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end
