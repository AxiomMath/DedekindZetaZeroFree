module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.ScalarLaplacianGraph

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.ExhaustionGeometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
  (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem component_injective (i : Fin a.componentCount) :
    Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)) := by
  intro x y h
  have he : a.components ⟨i,x⟩ = a.components ⟨i,y⟩ := by
    simpa only [a.components_formula] using h
  have hh := a.components.injective he
  cases hh
  rfl

 theorem end_height_bound (i : Fin a.componentCount) (c : Fin (a.cuspAtlas i).cuspCount)
    (z : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∃ B : ℝ, ∀ T : ℝ, B ≤ T → z ∉
      KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i))
          ((a.cuspAtlas i).representative c) T := by
  let A := a.cuspAtlas i
  let G := A.geometry c
  let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)
  let σ := A.representative c
  let q := A.cusp c
  let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
  let f := KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
  by_cases hz : z ∈ f '' KPFiniteCuspAtlas.endSet F Γ σ A.threshold
  · obtain ⟨y, hy, rfl⟩ := hz
    rw [← A.end_range c] at hy
    obtain ⟨v, rfl⟩ := hy
    let t := ((G.highPresentation A.threshold).symm v).2
    refine ⟨max A.threshold t.val, ?_⟩
    intro T hT hmem
    obtain ⟨y, ⟨x, ⟨w, hw, rfl⟩, rfl⟩, he⟩ := hmem
    let p := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).symm w
    have hp : KPCuspCharts.toArch F p = w :=
      (KPCuspCharts.toArchHomeomorph F G.positive_dimension).apply_symm_apply w
    have hpt : T < p.2 := by
      rw [← KPCuspCharts.toArch_meanHeight F G.positive_dimension p, hp]
      exact hw
    have hpa : A.threshold < p.2 := lt_of_le_of_lt ((le_max_left _ _).trans hT) hpt
    let v' : KPCuspCharts.HighQuotient F S A.threshold := Quotient.mk _ ⟨p,hpa⟩
    have hv : v' = v := (A.end_embedding c).injective
      (component_injective F ζ hζ hF U a i (by
        change f (KPCuspSiegel.projection F Γ (KPCuspSiegel.action F σ (KPCuspCharts.toArch F p))) = f _
        rw [hp]
        exact he))
    have ht : ((G.highPresentation A.threshold).symm v').2 = ⟨p.2,hpa⟩ := by
      have hh := G.highPresentation_formula A.threshold p.1 (⟨p.2,hpa⟩ : Set.Ioi A.threshold)
      have hh' : G.highPresentation A.threshold (Quotient.mk _ p.1, ⟨p.2,hpa⟩) = v' := hh
      rw [← hh', Homeomorph.symm_apply_apply]
    have ht' : t.val = p.2 := by
      dsimp [t]
      rw [← hv, ht]
    have := (le_max_right A.threshold t.val).trans hT
    rw [ht'] at this
    exact (not_lt_of_ge this) hpt
  · refine ⟨A.threshold, ?_⟩
    intro T hT hmem
    apply hz
    obtain ⟨y, ⟨x, ⟨w, hw, rfl⟩, rfl⟩, he⟩ := hmem
    refine ⟨_, ⟨_, ⟨w, ?_, rfl⟩, rfl⟩, he⟩
    exact lt_of_le_of_lt hT hw

 theorem eventually_not_highEnds (z : KPFiniteCuspAtlas.rawXU F ζ hζ U) :
    ∀ᶠ n : ℕ in atTop, z ∉ highEnds F ζ hζ hF U a n := by
  have hh : ∀ i : Fin a.componentCount, ∀ c : Fin (a.cuspAtlas i).cuspCount,
      ∀ᶠ n : ℕ in atTop, z ∉ KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i))
          ((a.cuspAtlas i).representative c) n := by
    intro i c
    obtain ⟨B,hB⟩ := end_height_bound F ζ hζ hF U a i c z
    exact (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop B)).mono fun n hn => hB n hn
  have hh' := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hh i))
  filter_upwards [hh'] with n hn
  simpa only [highEnds, Set.mem_iUnion, not_exists] using hn
end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.ExhaustionGeometry

end
