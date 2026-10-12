module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology

namespace DedekindZetaZeroFree.KPActualCollarBuffer

private theorem central_comm
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (ε : rootsOfUnity 3 F) (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

theorem actual_height_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (τ : ℝ) (hτ : A.threshold ≤ τ) :
    let I := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount
    let S := fun a : I => KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
      ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2)
    let L := fun (a : I) (z : KPCuspCharts.Coordinates F) =>
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z),
          A.representative a.1)
    let E := fun a : I =>
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).representative a.2) τ
    let t := fun (a : I) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) =>
      if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a z = x
      then (Classical.choose h).2 else 0
    (∀ a, L a '' {z : KPCuspCharts.Coordinates F | τ < z.2} = E a) ∧
    (∀ a (z : KPCuspCharts.Coordinates F), τ < z.2 → t a (L a z) = z.2) ∧
    (∀ a, ContinuousOn (t a) (E a)) ∧
    (∀ a, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : KPCuspCharts.Coordinates F => t a (L a z)) {z | τ < z.2}) ∧
    (∀ a (g : S a) (z : KPCuspCharts.Coordinates F), τ < z.2 →
      t a (L a (((A.cuspAtlas a.1).geometry a.2).crossAction g z.1, z.2)) =
        t a (L a z)) ∧
    (∀ a (g : S a) (B : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk B = (g : KPCuspArithmetic.PGL2 F) → B 1 0 = 0 →
      ∀ (z : KPCuspCharts.Coordinates F), τ < z.2 →
        let D := (A.cuspAtlas a.1).parabolic a.2
        let z' := KPCuspCharts.affine F hF D.E D.integralUnits
          (D.ratio g) (B 0 1 / B 1 1) z
        L a z' = L a z ∧ t a (L a z') = t a (L a z)) := by
  let I := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount
  let S := fun a : I => KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
    ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2)
  let L := fun (a : I) (z : KPCuspCharts.Coordinates F) =>
    Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z), A.representative a.1)
  let E := fun a : I =>
    KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
        ((A.cuspAtlas a.1).representative a.2) τ
  let t := fun (a : I) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) =>
    if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a z = x
    then (Classical.choose h).2 else 0
  change (∀ a : I, L a '' {z : KPCuspCharts.Coordinates F | τ < z.2} = E a) ∧
    (∀ (a : I) (z : KPCuspCharts.Coordinates F), τ < z.2 → t a (L a z) = z.2) ∧
    (∀ a : I, ContinuousOn (t a) (E a)) ∧
    (∀ a : I, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : KPCuspCharts.Coordinates F => t a (L a z)) {z | τ < z.2}) ∧
    (∀ (a : I) (g : S a) (z : KPCuspCharts.Coordinates F), τ < z.2 →
      t a (L a (((A.cuspAtlas a.1).geometry a.2).crossAction g z.1, z.2)) = t a (L a z)) ∧
    (∀ (a : I) (g : S a) (B : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk B = (g : KPCuspArithmetic.PGL2 F) → B 1 0 = 0 →
      ∀ (z : KPCuspCharts.Coordinates F), τ < z.2 →
        let D := (A.cuspAtlas a.1).parabolic a.2
        let z' := KPCuspCharts.affine F hF D.E D.integralUnits (D.ratio g) (B 0 1 / B 1 1) z
        L a z' = L a z ∧ t a (L a z') = t a (L a z))

  have key : ∀ (a : I) (z z' : KPCuspCharts.Coordinates F), τ < z.2 → τ < z'.2 →
      L a z = L a z' → z.2 = z'.2 := by
    intro a z z' hz hz' hL
    have hthr : (A.cuspAtlas a.1).threshold = A.threshold := A.common_threshold a.1
    have hzt : (A.cuspAtlas a.1).threshold < z.2 :=
      lt_of_le_of_lt (by rw [hthr]; exact hτ) hz
    have hzt' : (A.cuspAtlas a.1).threshold < z'.2 :=
      lt_of_le_of_lt (by rw [hthr]; exact hτ) hz'
    have e1 : L a z = KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)
        (KPFiniteCuspAtlas.endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ
          (Quotient.mk _ (⟨z, hz⟩ : {p : KPCuspCharts.Coordinates F // τ < p.2}))) := rfl
    have e2 : L a z' = KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)
        (KPFiniteCuspAtlas.endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ
          (Quotient.mk _ (⟨z', hz'⟩ : {p : KPCuspCharts.Coordinates F // τ < p.2}))) := rfl
    have hcomp : Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)) := by
      intro x y hxy
      have h1 : A.components ⟨a.1, x⟩ = A.components ⟨a.1, y⟩ := by
        rw [A.components_formula, A.components_formula]; exact hxy
      have h2 : (⟨a.1, x⟩ : (i : Fin A.componentCount) ×
          KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i)))
          = ⟨a.1, y⟩ := A.components.injective h1
      exact (by cases h2; rfl : x = y)
    have hEmap : KPFiniteCuspAtlas.endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ
          (Quotient.mk _ (⟨z, hz⟩ : {p : KPCuspCharts.Coordinates F // τ < p.2}))
        = KPFiniteCuspAtlas.endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) τ
          (Quotient.mk _ (⟨z', hz'⟩ : {p : KPCuspCharts.Coordinates F // τ < p.2})) :=
      hcomp (e1.symm.trans (hL.trans e2))
    have hp : KPCuspSiegel.projection F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          (KPCuspSiegel.action F ((A.cuspAtlas a.1).representative a.2) (KPCuspCharts.toArch F z))
        = KPCuspSiegel.projection F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          (KPCuspSiegel.action F ((A.cuspAtlas a.1).representative a.2) (KPCuspCharts.toArch F z')) := by
      simpa only [KPFiniteCuspAtlas.endMap, Quotient.lift_mk] using hEmap
    have hp0 : KPFiniteCuspAtlas.endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) (A.cuspAtlas a.1).threshold
          (Quotient.mk _ (⟨z, hzt⟩ : {p : KPCuspCharts.Coordinates F // (A.cuspAtlas a.1).threshold < p.2}))
        = KPFiniteCuspAtlas.endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          ((A.cuspAtlas a.1).cusp a.2) ((A.cuspAtlas a.1).representative a.2) (A.cuspAtlas a.1).threshold
          (Quotient.mk _ (⟨z', hzt'⟩ : {p : KPCuspCharts.Coordinates F // (A.cuspAtlas a.1).threshold < p.2})) := by
      simpa only [KPFiniteCuspAtlas.endMap, Quotient.lift_mk] using hp
    have hcls : Quotient.mk _ (⟨z, hzt⟩ : {p : KPCuspCharts.Coordinates F // (A.cuspAtlas a.1).threshold < p.2})
        = Quotient.mk _ (⟨z', hzt'⟩ : {p : KPCuspCharts.Coordinates F // (A.cuspAtlas a.1).threshold < p.2}) :=
      (A.cuspAtlas a.1).end_embedding a.2 |>.injective hp0
    let G := (A.cuspAtlas a.1).geometry a.2
    have hpair := congrArg (G.highPresentation (A.cuspAtlas a.1).threshold).symm hcls
    have hz1 : (G.highPresentation (A.cuspAtlas a.1).threshold).symm
          (Quotient.mk _ (⟨z, hzt⟩ : {p : KPCuspCharts.Coordinates F // (A.cuspAtlas a.1).threshold < p.2}))
        = (Quotient.mk _ z.1, (⟨z.2, hzt⟩ : Set.Ioi (A.cuspAtlas a.1).threshold)) := by
      conv_lhs => rw [← KPCuspCharts.ChartOutput.highPresentation_formula G (A.cuspAtlas a.1).threshold z.1
        (⟨z.2, hzt⟩ : Set.Ioi (A.cuspAtlas a.1).threshold)]
      exact (G.highPresentation (A.cuspAtlas a.1).threshold).symm_apply_apply _
    have hz1' : (G.highPresentation (A.cuspAtlas a.1).threshold).symm
          (Quotient.mk _ (⟨z', hzt'⟩ : {p : KPCuspCharts.Coordinates F // (A.cuspAtlas a.1).threshold < p.2}))
        = (Quotient.mk _ z'.1, (⟨z'.2, hzt'⟩ : Set.Ioi (A.cuspAtlas a.1).threshold)) := by
      conv_lhs => rw [← KPCuspCharts.ChartOutput.highPresentation_formula G (A.cuspAtlas a.1).threshold z'.1
        (⟨z'.2, hzt'⟩ : Set.Ioi (A.cuspAtlas a.1).threshold)]
      exact (G.highPresentation (A.cuspAtlas a.1).threshold).symm_apply_apply _
    have h2 := (Prod.mk.injEq _ _ _ _).mp (hz1.symm.trans (hpair.trans hz1'))
    exact congrArg Subtype.val h2.2
  have h2 : ∀ (a : I) (z : KPCuspCharts.Coordinates F), τ < z.2 → t a (L a z) = z.2 := by
    intro a z hz
    have hmem : ∃ z' : KPCuspCharts.Coordinates F, τ < z'.2 ∧ L a z' = L a z := ⟨z, hz, rfl⟩
    change (if h : ∃ z' : KPCuspCharts.Coordinates F, τ < z'.2 ∧ L a z' = L a z
      then (Classical.choose h).2 else 0) = z.2
    rw [dif_pos hmem]
    exact key a (Classical.choose hmem) z (Classical.choose_spec hmem).1 hz (Classical.choose_spec hmem).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨KPCuspSiegel.projection F (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
          (((A.cuspAtlas a.1).representative a.2) • KPCuspCharts.toArch F z), ?_, ?_⟩
      · refine ⟨((A.cuspAtlas a.1).representative a.2) • KPCuspCharts.toArch F z, ?_, rfl⟩
        refine ⟨KPCuspCharts.toArch F z, ?_, rfl⟩
        simpa only [Set.mem_setOf_eq,
          KPCuspCharts.toArch_meanHeight F ((A.cuspAtlas a.1).geometry a.2).positive_dimension] using hz
      · rfl
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨(KPCuspCharts.toArchHomeomorph F ((A.cuspAtlas a.1).geometry a.2).positive_dimension).symm u, ?_, ?_⟩
      · have hto : KPCuspCharts.toArch F
            ((KPCuspCharts.toArchHomeomorph F ((A.cuspAtlas a.1).geometry a.2).positive_dimension).symm u) = u :=
          (KPCuspCharts.toArchHomeomorph F ((A.cuspAtlas a.1).geometry a.2).positive_dimension).apply_symm_apply u
        have hh := KPCuspCharts.toArch_meanHeight F ((A.cuspAtlas a.1).geometry a.2).positive_dimension
            ((KPCuspCharts.toArchHomeomorph F ((A.cuspAtlas a.1).geometry a.2).positive_dimension).symm u)
        rw [hto] at hh
        simp only [Set.mem_setOf_eq]
        rw [← hh]
        simpa only [Set.mem_setOf_eq] using hu
      · have hto : KPCuspCharts.toArch F
            ((KPCuspCharts.toArchHomeomorph F ((A.cuspAtlas a.1).geometry a.2).positive_dimension).symm u) = u :=
          (KPCuspCharts.toArchHomeomorph F ((A.cuspAtlas a.1).geometry a.2).positive_dimension).apply_symm_apply u
        simp only [L, hto]
        rfl
  · exact h2
  ·
    intro a
    let C := A.cuspAtlas a.1
    let g := A.representative a.1
    let σ := C.representative a.2
    let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U g
    let G := C.geometry a.2
    have hcm : Topology.IsEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U g) := by
      have h1 : KPFiniteCuspAtlas.componentMap F ζ hζ U g = ⇑A.components ∘ (Sigma.mk a.1) := by
        funext x; rw [Function.comp_apply, A.components_formula]
      rw [h1]
      exact A.components.isEmbedding.comp (Topology.IsEmbedding.sigmaMk)
    have hend : Topology.IsEmbedding (KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ τ) := by
      let eT := KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ τ
      let e₀ := KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ C.threshold
      let inc : Set.Ioi τ → Set.Ioi C.threshold := fun t =>
        ⟨t.val, lt_of_le_of_lt (show C.threshold ≤ τ from by
          rw [A.common_threshold a.1]; exact hτ) t.property⟩
      have hinc : Topology.IsEmbedding inc := by
        apply Topology.IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
        exact Topology.IsEmbedding.subtypeVal
      have heq : eT ∘ G.highPresentation τ =
          e₀ ∘ G.highPresentation C.threshold ∘ Prod.map id inc := by
        funext x
        rcases x with ⟨p, t⟩
        induction p using Quotient.inductionOn with
        | h p => simp only [Function.comp_apply, Prod.map_apply, id_eq,
            KPCuspCharts.ChartOutput.highPresentation_formula]; rfl
      have hcomp : Topology.IsEmbedding (eT ∘ G.highPresentation τ) := by
        rw [heq]
        exact (C.end_embedding a.2).comp ((G.highPresentation C.threshold).isEmbedding.comp
          (Topology.IsEmbedding.id.prodMap hinc))
      have hfinal := hcomp.comp (G.highPresentation τ).symm.isEmbedding
      have heq' : (eT ∘ G.highPresentation τ) ∘ (G.highPresentation τ).symm = eT := by
        funext x; simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rwa [heq'] at hfinal
    let Ψ : KPCuspCharts.CrossQuotient F (S a) × Set.Ioi τ → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
      fun y => KPFiniteCuspAtlas.componentMap F ζ hζ U g
        (KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ τ (G.highPresentation τ y))
    have hΨ : Topology.IsEmbedding Ψ := hcm.comp (hend.comp (G.highPresentation τ).isEmbedding)
    have hrange : Set.range Ψ = E a := by
      have h1 : Set.range Ψ = KPFiniteCuspAtlas.componentMap F ζ hζ U g ''
          Set.range (KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ τ) := by
        rw [show Ψ = KPFiniteCuspAtlas.componentMap F ζ hζ U g ∘
              ((KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ τ) ∘ (G.highPresentation τ)) from rfl]
        rw [Set.range_comp, Set.range_comp, Set.range_eq_univ.mpr (G.highPresentation τ).surjective]
        simp
      rw [h1, KPFiniteCuspAtlas.endMap_range F G.positive_dimension Γ (C.cusp a.2) σ τ]
    rw [continuousOn_iff_continuous_restrict]
    let Ψ' : KPCuspCharts.CrossQuotient F (S a) × Set.Ioi τ ≃ₜ E a :=
      hΨ.toHomeomorph.trans (Homeomorph.setCongr hrange)
    have key2 : ∀ y, t a (Ψ y) = (y.2 : ℝ) := by
      rintro ⟨p, t'⟩
      induction p using Quotient.inductionOn with
      | h p =>
        have h1 : Ψ (Quotient.mk _ p, t') = L a (p, t'.val) := by
          show KPFiniteCuspAtlas.componentMap F ζ hζ U g
            (KPFiniteCuspAtlas.endMap F Γ (C.cusp a.2) σ τ
              ((G.highPresentation τ) (Quotient.mk _ p, t'))) = L a (p, t'.val)
          rw [KPCuspCharts.ChartOutput.highPresentation_formula]
          rfl
        rw [h1]
        exact h2 a (p, t'.val) t'.property
    have hx : ∀ x : E a, Ψ (Ψ'.symm x) = x.val := by
      intro x
      exact congrArg Subtype.val (Ψ'.apply_symm_apply x)
    have heq : (E a).domRestrict (t a) =
        (fun y : KPCuspCharts.CrossQuotient F (S a) × Set.Ioi τ => (y.2 : ℝ)) ∘ Ψ'.symm := by
      funext x
      simp only [Set.domRestrict, Function.comp_apply]
      rw [← hx x, key2]
    rw [heq]
    exact (continuous_subtype_val.comp continuous_snd).comp Ψ'.symm.continuous
  ·
    intro a
    refine (contDiff_snd (𝕜 := ℝ) (E := KPCuspCharts.Cross F) (F := ℝ)).contDiffOn.congr ?_
    intro z hz
    exact h2 a z hz
  ·
    intro a g z hz
    rw [h2 a (((A.cuspAtlas a.1).geometry a.2).crossAction g z.1, z.2) hz, h2 a z hz]
  ·
    intro a g B hB hB10 z hz
    let C := A.cuspAtlas a.1
    let g' := A.representative a.1
    let σ := C.representative a.2
    let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U g'
    let D := C.parabolic a.2
    let z' := KPCuspCharts.affine F hF D.E D.integralUnits (D.ratio g) (B 0 1 / B 1 1) z
    change L a z' = L a z ∧ t a (L a z') = t a (L a z)
    constructor
    · let γ := KPCuspGenuineMonodromy.cuspInclusion F Γ (C.cusp a.2) σ g
      have hγ : (↑γ : KPCuspArithmetic.PGL2 F) = σ * (g : KPCuspArithmetic.PGL2 F) * σ⁻¹ :=
        KPCuspGenuineMonodromy.cuspInclusion_formula F Γ (C.cusp a.2) σ g
      have hact := (C.geometry a.2).actual_action g B hB hB10 z
      have h1 : σ • KPCuspCharts.toArch F z' = (↑γ : KPCuspArithmetic.PGL2 F) • (σ • KPCuspCharts.toArch F z) := by
        rw [hγ]
        simp only [mul_smul, inv_smul_smul]
        rw [show KPCuspCharts.toArch F z' = KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F)
            (KPCuspCharts.toArch F z) from hact.symm]
        rfl
      obtain ⟨ε, u, hu⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U g' γ
      have hstep : KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
            KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (↑γ : KPCuspArithmetic.PGL2 F) * g'
          = g' * ↑u := by
        calc KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
              KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (↑γ : KPCuspArithmetic.PGL2 F) * g'
            = KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
                (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (↑γ : KPCuspArithmetic.PGL2 F) * g') := by
              rw [mul_assoc]
          _ = KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
                (KPCuspGenuineMonodromy.central F ζ hζ ε * g' * ↑u) := by rw [hu]
          _ = g' * ↑u := by rw [← mul_assoc, ← mul_assoc, map_inv, inv_mul_cancel, one_mul]
      have hrel : g' = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (↑γ : KPCuspArithmetic.PGL2 F) *
          KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ * g' * (↑u)⁻¹ := by
        rw [show KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (↑γ : KPCuspArithmetic.PGL2 F) *
              KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹
            = KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
              KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ (↑γ : KPCuspArithmetic.PGL2 F)
            from (central_comm F ζ hζ ε⁻¹ _).symm]
        rw [hstep]
        group
      exact (Quotient.sound (s := KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
        ⟨(↑γ : KPCuspArithmetic.PGL2 F), ε⁻¹, u⁻¹, h1, hrel⟩).symm
    · have hz' : τ < z'.2 := lt_of_lt_of_eq hz
          (KPCuspCharts.affine_radial F hF D.E D.integralUnits (D.ratio g) (B 0 1 / B 1 1) z).symm
      rw [h2 a z' hz', h2 a z hz]
      exact KPCuspCharts.affine_radial F hF D.E D.integralUnits (D.ratio g) (B 0 1 / B 1 1) z

end DedekindZetaZeroFree.KPActualCollarBuffer

end
