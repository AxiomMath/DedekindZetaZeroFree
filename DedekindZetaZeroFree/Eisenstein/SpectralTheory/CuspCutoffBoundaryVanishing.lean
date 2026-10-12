module

public import DedekindZetaZeroFree.Geometry.Cusps.MeanHeightDescent
public import DedekindZetaZeroFree.Eisenstein.Continuation.Cusps.CutoffSourceData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPActualCollarBuffer

 def rowDen (r : ℂ × ℂ) (z : KPArch.H3) : ℝ :=
  ‖r.1 * z.1 + r.2‖ ^ 2 + ‖r.1‖ ^ 2 * (Real.exp z.2) ^ 2
private lemma rowDen_pos (r : ℂ × ℂ) (hr : r ≠ 0) (z : KPArch.H3) :
    0 < rowDen r z := by
  by_cases hc : r.1 = 0
  · have hd : r.2 ≠ 0 := by
      intro hd
      exact hr (Prod.ext hc hd)
    simpa [rowDen, hc] using sq_pos_of_pos (norm_pos_iff.mpr hd)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hc)) (sq_pos_of_pos (Real.exp_pos _)))
private lemma rowDen_cont : Continuous (fun p : KPArch.H3 × (ℂ × ℂ) => rowDen p.2 p.1) := by
  unfold rowDen
  fun_prop
private lemma rowDen_smul (s : ℝ) (r : ℂ × ℂ) (z : KPArch.H3) :
    rowDen (s • r) z = ‖s‖ ^ 2 * rowDen r z := by
  simp only [rowDen, Prod.smul_fst, Prod.smul_snd, smul_mul_assoc, ← smul_add,
    norm_smul, Real.norm_eq_abs]
  ring
 def rowBusemann (z : KPArch.H3) (r : ℂ × ℂ) : ℝ := z.2 - Real.log (rowDen r z)
private lemma uniform_local_busemann (z : KPArch.H3) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 z, ∀ w ∈ V, ∀ r : ℂ × ℂ, ‖r‖ = 1 →
      |rowBusemann w r - rowBusemann z r| < ε := by
  have hc : IsCompact (Metric.sphere (0 : ℂ × ℂ) 1) := isCompact_sphere _ _
  have hf : ContinuousOn (Function.uncurry rowBusemann)
      (Set.univ ×ˢ Metric.sphere (0 : ℂ × ℂ) 1) := by
    change ContinuousOn (fun p : KPArch.H3 × (ℂ × ℂ) => p.1.2 - Real.log (rowDen p.2 p.1)) _
    apply ContinuousOn.sub continuous_fst.snd.continuousOn
    apply rowDen_cont.continuousOn.log
    rintro ⟨w, r⟩ ⟨_, hr⟩
    apply (rowDen_pos r ?_ w).ne'
    have hr1 : ‖r‖ = 1 := by simpa using hr
    intro h
    simpa [h] using hr1
  have hu : {p : ℝ × ℝ | |p.1 - p.2| < ε} ∈ uniformity ℝ := by
    convert Metric.dist_mem_uniformity (α := ℝ) hε using 1
  obtain ⟨V, hV, hv⟩ := hc.mem_uniformity_of_prod hf (Set.mem_univ z) hu
  refine ⟨V, by simpa using hV, ?_⟩
  intro w hw r hr
  exact hv w hw r (by simpa using hr)
private lemma uniform_local_action_height (z : KPArch.H3) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 z, ∀ w ∈ V, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
      |(KPArch.action g w).2 - (KPArch.action g z).2| < ε := by
  obtain ⟨V, hV, hv⟩ := uniform_local_busemann z ε hε
  refine ⟨V, hV, ?_⟩
  intro w hw g
  let r : ℂ × ℂ := (g 1 0, g 1 1)
  have hr : r ≠ 0 := by
    intro h
    have hc : g 1 0 = 0 := congrArg Prod.fst h
    have hd : g 1 1 = 0 := congrArg Prod.snd h
    exact g.det_ne_zero (by simp [Matrix.det_fin_two, hc, hd])
  have hn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hs : 0 < ‖r‖⁻¹ := inv_pos.mpr hn
  have hrn : ‖(‖r‖⁻¹ : ℝ) • r‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, inv_mul_cancel₀ hn.ne']
  have he := hv w hw ((‖r‖⁻¹ : ℝ) • r) hrn
  have hlog (q : KPArch.H3) :
      rowBusemann q ((‖r‖⁻¹ : ℝ) • r) =
        rowBusemann q r - Real.log (‖(‖r‖⁻¹ : ℝ)‖ ^ 2) := by
    rw [rowBusemann, rowDen_smul, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hs.ne'))
      (rowDen_pos r hr q).ne']
    unfold rowBusemann
    ring
  have hact (q : KPArch.H3) :
      (KPArch.action g q).2 = Real.log ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ + rowBusemann q r := by
    change Real.log (‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ * Real.exp q.2 / rowDen r q) = _
    rw [Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr g.det_ne_zero) (Real.exp_ne_zero _))
      (rowDen_pos r hr q).ne', Real.log_mul (norm_ne_zero_iff.mpr g.det_ne_zero)
      (Real.exp_ne_zero _), Real.log_exp]
    unfold rowBusemann
    ring
  rw [hlog w, hlog z] at he
  rw [hact w, hact z]
  convert he using 1 <;> congr 1 <;> ring
private lemma uniform_local_mean_height (F : Type*) [Field F] [NumberField F]
    (z : KPArch.Space (KPCuspLogShape.dimension F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 z, ∀ w ∈ V, ∀ g : KPCuspArithmetic.PGL2 F,
      |KPCuspLogShape.meanHeight _ (g • w) - KPCuspLogShape.meanHeight _ (g • z)| < ε := by
  let d := KPCuspLogShape.dimension F
  have hp (i : Fin d) := uniform_local_action_height (z i) (ε / (d + 1)) (by positivity)
  choose V hV hv using hp
  let W : Set (KPArch.Space d) := {w | ∀ i, w i ∈ V i}
  have hW : W ∈ 𝓝 z := by
    exact Filter.mem_of_superset (Filter.iInter_mem.mpr (fun i => (continuous_apply i).continuousAt.preimage_mem_nhds (hV i)))
      (by intro w hw; exact Set.mem_iInter.mp hw)
  refine ⟨W, hW, ?_⟩
  intro w hw g
  obtain ⟨G, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  simp only [show (Matrix.ProjGenLinGroup.mk G) • w = KPCuspSiegel.glAction F G w from KPCuspSiegel.action_mk F G w,
    show (Matrix.ProjGenLinGroup.mk G) • z = KPCuspSiegel.glAction F G z from KPCuspSiegel.action_mk F G z]
  change |(∑ i, (KPArch.action _ (w i)).2) / d - (∑ i, (KPArch.action _ (z i)).2) / d| < ε
  by_cases hd : d = 0
  · simp [hd, hε]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [← sub_div, abs_div, abs_of_pos hdpos]
  apply (div_lt_iff₀ hdpos).mpr
  calc
    |(∑ i, (KPArch.action _ (w i)).2) - ∑ i, (KPArch.action _ (z i)).2| =
        |∑ i, ((KPArch.action _ (w i)).2 - (KPArch.action _ (z i)).2)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, |(KPArch.action _ (w i)).2 - (KPArch.action _ (z i)).2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ε / (d + 1) := Finset.sum_le_sum (fun i _ => (hv i (w i) (hw i) _).le)
    _ < ε * d := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : ε / ((d : ℝ) + 1) < ε := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
      nlinarith

private theorem cutoff_two_jets_zero {T r : ℝ}
    (χ : KPCutoffSource.SmoothCuspCutoff T) (hr : r < T) :
    χ.toFun r = 0 ∧ deriv χ.toFun r = 0 ∧ deriv (deriv χ.toFun) r = 0 := by
  have heq : χ.toFun =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hr] with q hq
    exact χ.zero_below q (le_of_lt hq)
  have hd : deriv χ.toFun =ᶠ[𝓝 r] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [heq.deriv] with q hq
    simpa only [deriv_const] using hq
  exact ⟨χ.zero_below r (le_of_lt hr), by simpa using heq.deriv_eq,
    by simpa using hd.deriv_eq⟩

theorem actual_boundary_zero_buffer
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (τ T : ℝ) (hτ : A.threshold ≤ τ) (hT : τ < T) :
    let I := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount
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
    (∀ a x, x ∈ frontier (E a) →
      ∃ V : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, y ∈ E a → t a y < T) ∧
    (∀ a x, x ∈ frontier (E a) →
      ∃ V : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsOpen V ∧ x ∈ V ∧
        ∀ (χ : KPCutoffSource.SmoothCuspCutoff T) y, y ∈ V →
          (E a).indicator (fun y => χ.toFun (t a y)) y = 0 ∧
          (E a).indicator (fun y => deriv χ.toFun (t a y)) y = 0 ∧
          (E a).indicator (fun y => deriv (deriv χ.toFun) (t a y)) y = 0) := by
  dsimp only
  let I := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount
  let L := fun (a : I) (z : KPCuspCharts.Coordinates F) =>
    Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
      (((A.cuspAtlas a.1).representative a.2 • KPCuspCharts.toArch F z), A.representative a.1)
  let E := fun a : I => KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1))
      ((A.cuspAtlas a.1).representative a.2) τ
  let t := fun (a : I) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) =>
    if h : ∃ z : KPCuspCharts.Coordinates F, τ < z.2 ∧ L a z = x
    then (Classical.choose h).2 else 0
  obtain ⟨hrange, hcoord, -, -, -, -⟩ := actual_height_descent F ζ hζ hF U A τ hτ
  have hd := KPCuspCharts.positive_dimension F hF
  have hbuffer : ∀ (a : I) x, x ∈ frontier (E a) →
      ∃ V : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V, y ∈ E a → t a y < T := by
    intro a x hx
    let Γ := KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative a.1)
    let σ := (A.cuspAtlas a.1).representative a.2
    let c := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative a.1)
    have hopenc : IsOpenMap c := by
      have he := A.components.isOpenMap.comp (isOpenMap_sigmaMk (i := a.1))
      simpa only [c, Function.comp_def, A.components_formula] using he
    have hclosedc : IsClosed (Set.range c) := by
      have he := A.components.isClosedMap.comp (isClosedMap_sigmaMk (i := a.1))
      have he' : IsClosedMap c := by
        simpa only [c, Function.comp_def, A.components_formula] using he
      exact he'.isClosed_range
    have hinj : Function.Injective c := by
      intro p q hpq
      have he : A.components ⟨a.1, p⟩ = A.components ⟨a.1, q⟩ := by
        simpa only [A.components_formula] using hpq
      cases A.components.injective he
      rfl
    have hopenE : IsOpen (E a) := hopenc _ (KPFiniteAdelicCuspEnds.component_open_end F Γ σ τ)
    have hxnot : x ∉ E a := by
      simpa only [hopenE.interior_eq] using hx.2
    have hxrange : x ∈ Set.range c :=
      (closure_minimal (by rintro y ⟨p, _, rfl⟩; exact ⟨p, rfl⟩) hclosedc) hx.1
    obtain ⟨p, hp⟩ := hxrange
    obtain ⟨z, hz⟩ := Quotient.mk_surjective p
    have hxz : c (KPCuspSiegel.projection F Γ z) = x := (congrArg c hz).trans hp
    have hbelow : ∀ g : KPCuspArithmetic.PGL2 F,
        (∃ γ : Γ, g = σ⁻¹ * γ.val) → KPCuspLogShape.meanHeight _ (g • z) ≤ τ := by
      rintro g ⟨γ, rfl⟩
      by_contra hb
      apply hxnot
      refine ⟨KPCuspSiegel.projection F Γ z, ?_, hxz⟩
      refine ⟨γ.val • z, ?_, ?_⟩
      · change γ.val • z ∈ KPCuspSiegel.highCusp F σ τ
        refine ⟨σ⁻¹ • (γ.val • z), ?_, ?_⟩
        · change τ < KPCuspLogShape.meanHeight _ (σ⁻¹ • (γ.val • z))
          simpa only [mul_smul] using lt_of_not_ge hb
        · change σ • (σ⁻¹ • (γ.val • z)) = γ.val • z
          simp
      · apply Quotient.sound
        apply MulAction.orbitRel_apply.mpr
        apply MulAction.mem_orbit_iff.mpr
        exact ⟨γ, rfl⟩
    obtain ⟨W, hW, hWbound⟩ := uniform_local_mean_height F z (T - τ) (sub_pos.mpr hT)
    obtain ⟨W₀, hsub, hopenW, hzW⟩ := mem_nhds_iff.mp hW
    refine ⟨c '' (KPCuspSiegel.projection F Γ '' W₀),
      hopenc _ (KPCuspSiegel.isOpenMap_projection F Γ _ hopenW),
      ⟨_, ⟨z, hzW, rfl⟩, hxz⟩, ?_⟩
    intro y hy hye
    obtain ⟨p', ⟨w, hw, hwp⟩, hpy⟩ := hy
    obtain ⟨q, hq, hqy⟩ := (show y ∈ L a '' {q | τ < q.2} from (hrange a).symm ▸ hye)
    have hval : t a y = q.2 := hqy ▸ hcoord a q hq
    rw [hval]
    have he : KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F q) =
        KPCuspSiegel.projection F Γ w := by
      apply hinj
      change L a q = c (KPCuspSiegel.projection F Γ w)
      exact hqy.trans ((congrArg c hwp).trans hpy).symm
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact he))
    have heq : (σ⁻¹ * γ.val) • w = KPCuspCharts.toArch F q := by
      rw [mul_smul]
      change σ⁻¹ • (γ • w) = _
      rw [hγ]
      simp
    have hb := hbelow (σ⁻¹ * γ.val) ⟨γ, rfl⟩
    have hb' := hWbound w (hsub hw) (σ⁻¹ * γ.val)
    rw [heq, KPCuspCharts.toArch_meanHeight F hd] at hb'
    have := (abs_lt.mp hb').2
    linarith
  refine ⟨hbuffer, ?_⟩
  intro a x hx
  obtain ⟨V, hV, hxV, hbelow⟩ := hbuffer a x hx
  refine ⟨V, hV, hxV, ?_⟩
  intro χ y hy
  change (E a).indicator (fun y => χ.toFun (t a y)) y = 0 ∧
    (E a).indicator (fun y => deriv χ.toFun (t a y)) y = 0 ∧
    (E a).indicator (fun y => deriv (deriv χ.toFun) (t a y)) y = 0
  by_cases hE : y ∈ E a
  · obtain ⟨h0, h1, h2⟩ := cutoff_two_jets_zero χ (hbelow y hy hE)
    simpa only [Set.indicator_of_mem hE] using And.intro h0 (And.intro h1 h2)
  · simp only [Set.indicator_of_notMem hE, and_self]

end DedekindZetaZeroFree.KPActualCollarBuffer

end
