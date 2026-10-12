module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellRestriction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TranslatedBorelCellPartitions

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPActualResidueSources

open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneOpenCellKernel
open KPRankOneCenterInducedDiagonalComparison KPRankOneReverseRegulatorShells
open KPActualScalarBinding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable (S : ActualKPBinding F ζ hζ q) (P : Polarization S.heisenberg)
variable [DecidableEq S.D]

omit [DecidableEq S.D] in

theorem center_compact_level_global_fixed
    (J : CompactOpenLevel (Cover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup) (z : ℂ)
    (a : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z)
    (ha : (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel
      S.iwasawa .plus z).symm a ∈
      centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus J) :
    ∀ (j : J.toOpenSubgroup) (x : Cover F ζ hζ q), a.val (x * j.val) = a.val x := by
  intro j x
  let k := S.iwasawa.compactPart x
  let kj : S.iwasawa.compact.toOpenSubgroup := ⟨k.val * j.val,
    S.iwasawa.compact.toOpenSubgroup.mul_mem k.property (hJ j.property)⟩
  have hk := ha j k kj rfl
  change a.val kj.val = a.val k.val at hk
  rw [S.iwasawa.decomposition x]
  rw [mul_assoc, a.property.1, a.property.1]
  exact congrArg (centerInducingAction F ζ hζ q S.heisenberg S.borel .plus z
    (S.iwasawa.borelPart x)) hk

def center_conjugate_common_level
    {N : ℕ} (J : CompactOpenLevel (Cover F ζ hζ q))
    (J₀ : Fin N → CompactOpenLevel (Cover F ζ hζ q))
    (g : Fin N → Cover F ζ hζ q) : CompactOpenLevel (Cover F ζ hζ q) :=
  let U := J.toOpenSubgroup ⊓ Finset.univ.inf (fun i : Fin N => (J₀ i).toOpenSubgroup.comap
    (MulAut.conj (g i)⁻¹).toMonoidHom
    (by change Continuous (fun x : Cover F ζ hζ q => (g i)⁻¹ * x * ((g i)⁻¹)⁻¹); fun_prop))
  ⟨U, J.isCompact.of_isClosed_subset U.isClosed (fun _ hx => hx.1)⟩

theorem center_conjugate_common_level_le
    {N : ℕ} (J : CompactOpenLevel (Cover F ζ hζ q))
    (J₀ : Fin N → CompactOpenLevel (Cover F ζ hζ q))
    (g : Fin N → Cover F ζ hζ q) :
    (center_conjugate_common_level F ζ hζ q J J₀ g).toOpenSubgroup ≤ J.toOpenSubgroup :=
  inf_le_left

theorem center_conjugate_common_level_le_conjugate
    {N : ℕ} (J : CompactOpenLevel (Cover F ζ hζ q))
    (J₀ : Fin N → CompactOpenLevel (Cover F ζ hζ q))
    (g : Fin N → Cover F ζ hζ q) (i : Fin N) :
    (center_conjugate_common_level F ζ hζ q J J₀ g).toOpenSubgroup ≤
      (J₀ i).toOpenSubgroup.comap (MulAut.conj (g i)⁻¹).toMonoidHom
      (by change Continuous (fun x : Cover F ζ hζ q => (g i)⁻¹ * x * ((g i)⁻¹)⁻¹); fun_prop) :=
  inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))

omit [DecidableEq S.D] in

theorem center_translated_common_level_fixed
    {N : ℕ} (J : CompactOpenLevel (Cover F ζ hζ q))
    (J₀ : Fin N → CompactOpenLevel (Cover F ζ hζ q))
    (hJ₀ : ∀ i, (J₀ i).toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup)
    (g : Fin N → Cover F ζ hζ q) (z : ℂ)
    (a : Fin N → centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z)
    (ha : ∀ i, (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel
      S.iwasawa .plus z).symm (a i) ∈
      centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus (J₀ i)) :
    ∀ i, (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel
      S.iwasawa .plus z).symm
      (centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus z (g i) (a i)) ∈
      centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus
        (center_conjugate_common_level F ζ hζ q J J₀ g) := by
  intro i j k k' hk
  let jg : (J₀ i).toOpenSubgroup := ⟨(g i)⁻¹ * j.val * (g i), by
    have hj := center_conjugate_common_level_le_conjugate F ζ hζ q J J₀ g i j.property
    change (g i)⁻¹ * j.val * ((g i)⁻¹)⁻¹ ∈ (J₀ i).toOpenSubgroup at hj
    simpa only [inv_inv] using hj⟩
  have h := center_compact_level_global_fixed F ζ hζ q S (J₀ i) (hJ₀ i) z
    (a i) (ha i) jg (k.val * g i)
  change (a i).val (k'.val * g i) = (a i).val (k.val * g i)
  rw [hk]
  simpa [jg, mul_assoc] using h

theorem actual_pure_sections_individual_and_translated_levels
    {N : ℕ} (J : CompactOpenLevel (Cover F ζ hζ q))
    (g : Fin N → Cover F ζ hζ q)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (d : Fin N → S.D)
    (φ : Fin N → LocalField F q → ℂ)
    (hφ : ∀ i, IsLocallyConstant (φ i)) (hcφ : ∀ i, HasCompactSupport (φ i)) (r : ℂˣ) :
    ∃ (J₀ : Fin N → CompactOpenLevel (Cover F ζ hζ q))
      (L : CompactOpenLevel (Cover F ζ hζ q)),
      L.toOpenSubgroup ≤ J.toOpenSubgroup ∧
      (∀ i, (J₀ i).toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup) ∧
      (∀ i, L.toOpenSubgroup ≤ (J₀ i).toOpenSubgroup.comap
        (MulAut.conj (g i)⁻¹).toMonoidHom
        (by change Continuous (fun x : Cover F ζ hζ q => (g i)⁻¹ * x * ((g i)⁻¹)⁻¹); fun_prop)) ∧
      (let a := fun i => actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep (d i) (φ i) (hφ i) (hcφ i) r
       (∀ i, (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa
          .plus (additiveParameter F q r)).symm (a i) ∈
          centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus (J₀ i)) ∧
       (∀ i, (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa
          .plus (additiveParameter F q r)).symm
          (centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus
            (additiveParameter F q r) (g i) (a i)) ∈
          centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus L)) := by
  classical
  let a := fun i => actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
    rep hrep (d i) (φ i) (hφ i) (hcφ i) r
  have hlevels := fun i => centerSection_has_compact_level F ζ hζ q S.heisenberg S.borel
    S.iwasawa .plus (additiveParameter F q r) (a i)
  choose J₀ hJ₀ v hv using hlevels
  have ha : ∀ i, (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa
      .plus (additiveParameter F q r)).symm (a i) ∈
      centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus (J₀ i) := by
    intro i
    rw [← hv i, LinearEquiv.symm_apply_apply]
    exact (v i).property
  exact ⟨J₀, center_conjugate_common_level F ζ hζ q J J₀ g,
    center_conjugate_common_level_le F ζ hζ q J J₀ g, hJ₀,
    center_conjugate_common_level_le_conjugate F ζ hζ q J J₀ g,
    ha, center_translated_common_level_fixed F ζ hζ q S J J₀ hJ₀ g
      (additiveParameter F q r) a ha⟩

theorem actual_cell_finite_center_coordinate_expansion
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (r : ℂˣ)
    (a : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus (additiveParameter F q r))
    (hc : HasCompactSupport (fun x : LocalField F q =>
      a.val (openCoordinate F ζ hζ q x)))
    (hzero : ∀ g : Cover F ζ hζ q,
      (¬ ∃ (b : S.borel.B) (x : LocalField F q),
        g = (b : Cover F ζ hζ q) * openCoordinate F ζ hζ q x) → a.val g = 0) :
    ∃ (φ : S.D → LocalField F q → ℂ)
      (hφ : ∀ d, IsLocallyConstant (φ d)) (hcφ : ∀ d, HasCompactSupport (φ d)),
      a = ∑ d ∈ (Set.toFinite (Set.univ : Set S.D)).toFinset,
        actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep d (φ d) (hφ d) (hcφ d) r := by
  classical
  let := Fintype.ofFinite S.D
  let p : LocalField F q → CenterModule S.heisenberg :=
    fun x => a.val (openCoordinate F ζ hζ q x)
  let φ : S.D → LocalField F q → ℂ := fun d x =>
    centerCoordinates S.heisenberg rep hrep (p x) d
  have hl := center_section_affine_locallyConstant F ζ hζ q S.heisenberg S.borel P
    (S.openCell P) .plus (additiveParameter F q r) a
  have hφ : ∀ d, IsLocallyConstant (φ d) := fun d =>
    hl.comp (fun v => centerCoordinates S.heisenberg rep hrep v d)
  have hcφ : ∀ d, HasCompactSupport (φ d) := fun d =>
    hc.comp_left (g := fun v => centerCoordinates S.heisenberg rep hrep v d) (by simp)
  refine ⟨φ, hφ, hcφ, ?_⟩
  have hsum : (Set.toFinite (Set.univ : Set S.D)).toFinset = Finset.univ := by ext; simp
  rw [hsum]
  refine centerSection_open_cell_ext F ζ hζ q S.heisenberg S.borel .plus
    (additiveParameter F q r) a _ ?_ hzero ?_
  · intro x
    apply (centerCoordinates S.heisenberg rep hrep).injective
    simp only [Submodule.coe_sum, Finset.sum_apply, map_sum]
    trans ∑ d : S.D, φ d x • Pi.single d 1
    · ext d
      simp [φ, Pi.single_apply, p]
    · apply Finset.sum_congr rfl
      intro d hd
      exact (actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d (φ d) (hφ d) (hcφ d) r).1 x |>.symm
  · intro g hg
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro d hd
    exact (actualSection_spec F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep d (φ d) (hφ d) (hcφ d) r).2 g hg

open scoped Topology

omit [DecidableEq S.D] in
private theorem center_scalar_lc (z : ℂ)
    (a : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z) :
    IsLocallyConstant a.val := by
  obtain ⟨U,hU⟩ := a.property.2
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous (fun y : Cover F ζ hζ q => x⁻¹*y) := continuous_const.mul continuous_id
  have hm : ∀ᶠ y : Cover F ζ hζ q in nhds x, x⁻¹*y ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by simpa using U.isOpen.mem_nhds U.one_mem)
  filter_upwards [hm] with y hy
  have he := congrFun (hU (x⁻¹*y) hy) x
  simpa [vectorRightTranslation, mul_assoc] using he

omit [DecidableEq S.D] in
private theorem cell_cut_section (z : ℂ)
    (a : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z)
    (g : Cover F ζ hζ q) (E : Set (Cover F ζ hζ q)) (hE : IsClopen E)
    (hB : ∀ (b : S.borel.B) x, b.val*x ∈ E ↔ x ∈ E)
    (hcell : ∀ x ∈ E, ∃ (b : S.borel.B) (s : LocalField F q),
      x = b.val * openCoordinate F ζ hζ q s * g⁻¹)
    (hc : IsCompact {s : LocalField F q | openCoordinate F ζ hζ q s * g⁻¹ ∈ E}) :
    ∃ v : centerSectionSpace F ζ hζ q S.heisenberg S.borel .plus z,
      (∀ x, v.val x = E.indicator a.val (x*g⁻¹)) ∧
      HasCompactSupport (fun s : LocalField F q => v.val (openCoordinate F ζ hζ q s)) ∧
      (∀ x : Cover F ζ hζ q,
        (¬ ∃ (b : S.borel.B) (s : LocalField F q), x = b.val*openCoordinate F ζ hζ q s) →
        v.val x = 0) := by
  classical
  let v : Cover F ζ hζ q → CenterModule S.heisenberg :=
    fun x => if x*g⁻¹ ∈ E then a.val (x*g⁻¹) else 0
  have hv : ∀ (b : S.borel.B) x,
      v (b.val*x) = centerInducingAction F ζ hζ q S.heisenberg S.borel .plus z b (v x) := by
    intro b x
    dsimp [v]
    rw [mul_assoc]
    by_cases hx : x*g⁻¹ ∈ E <;> simp [hB b (x*g⁻¹), hx, a.property.1]
  have hl : IsLocallyConstant v := by
    have he : IsClopen ((fun x : Cover F ζ hζ q => x*g⁻¹) ⁻¹' E) :=
      hE.preimage (continuous_id.mul continuous_const)
    have ha := (center_scalar_lc F ζ hζ q S z a).comp_continuous
      (continuous_id.mul continuous_const : Continuous (fun x : Cover F ζ hζ q => x*g⁻¹))
    have hl := (LocallyConstant.indicator
      (⟨fun x : Cover F ζ hζ q => a.val (x*g⁻¹),ha⟩ :
        LocallyConstant (Cover F ζ hζ q) (CenterModule S.heisenberg)) he).isLocallyConstant
    convert hl using 1
    funext x
    simp [LocallyConstant.indicator, Set.indicator_apply, v]
  have hz : ∀ x : Cover F ζ hζ q,
      (¬ ∃ (b : S.borel.B) (s : LocalField F q), x = b.val*openCoordinate F ζ hζ q s) → v x = 0 := by
    intro x hx
    dsimp [v]
    split_ifs with hm
    · obtain ⟨b,s,he⟩ := hcell (x*g⁻¹) hm
      exact (hx ⟨b,s,by simpa [mul_assoc] using congrArg (fun x => x*g) he⟩).elim
    · rfl
  have hp : HasCompactSupport (fun s : LocalField F q => v (openCoordinate F ζ hζ q s)) := by
    apply HasCompactSupport.intro hc
    intro s hs
    dsimp [v]
    simp only [Set.mem_ofPred_eq] at hs
    simp [hs]
  have hcont : Continuous (openCoordinate F ζ hζ q) := by
    have hn := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
    exact continuous_const.mul hn
  have hrep : ∀ x : Cover F ζ hζ q, v x ≠ 0 →
      ∃ (b : S.borel.B) (c : Cover F ζ hζ q),
        c ∈ openCoordinate F ζ hζ q '' tsupport
          (fun s : LocalField F q => v (openCoordinate F ζ hζ q s)) ∧ x = b.val*c := by
    intro x hx
    by_cases h : ∃ (b : S.borel.B) (s : LocalField F q), x = b.val*openCoordinate F ζ hζ q s
    · obtain ⟨b,s,rfl⟩ := h
      refine ⟨b,openCoordinate F ζ hζ q s,⟨s,?_,rfl⟩,rfl⟩
      apply subset_closure
      rw [Function.mem_support]
      intro h0
      exact hx (by rw [hv,h0,map_zero])
    · exact (hx (hz x h)).elim
  have hs := KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps.covariant_smooth_of_compact_representatives
    S.borel.B (centerInducingAction F ζ hζ q S.heisenberg S.borel .plus z) v hv hl
    _ (hp.isCompact.image hcont) hrep
  exact ⟨⟨v,hv,hs⟩,fun _ => by simp [v, Set.indicator_apply],hp,hz⟩

theorem actual_center_compact_translated_pure_spanning
    (J : CompactOpenLevel (Cover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup)
    (rep : S.D → KPExceptionalRaw.actualTorus F ζ hζ q)
    (hrep : ∀ d, S.heisenberg.π (rep d) = d) (r : ℂˣ)
    (f : centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus J) :
    ∃ (N : ℕ) (g : Fin N → Cover F ζ hζ q) (d : Fin N → S.D)
      (φ : Fin N → LocalField F q → ℂ)
      (hφ : ∀ i, IsLocallyConstant (φ i)) (hcφ : ∀ i, HasCompactSupport (φ i))
      (J₀ : Fin N → CompactOpenLevel (Cover F ζ hζ q))
      (L : CompactOpenLevel (Cover F ζ hζ q)),
      L.toOpenSubgroup ≤ J.toOpenSubgroup ∧
      (∀ i, (J₀ i).toOpenSubgroup ≤ S.iwasawa.compact.toOpenSubgroup) ∧
      (∀ i, L.toOpenSubgroup ≤ (J₀ i).toOpenSubgroup.comap
        (MulAut.conj (g i)⁻¹).toMonoidHom
        (by change Continuous (fun x : Cover F ζ hζ q => (g i)⁻¹ * x * ((g i)⁻¹)⁻¹); fun_prop)) ∧
      (let a := fun i => actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
          rep hrep (d i) (φ i) (hφ i) (hcφ i) r
       let a₀ := fun i => (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel
          S.iwasawa .plus (additiveParameter F q r)).symm (a i)
       let a₁ := fun i => (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel
          S.iwasawa .plus (additiveParameter F q r)).symm
          (centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus (additiveParameter F q r)
            (g i) (a i))
       (∀ i, a₀ i ∈ centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus (J₀ i)) ∧
       (∀ i, a₁ i ∈ centerCompactLevel F ζ hζ q S.heisenberg S.borel S.iwasawa .plus L) ∧
       f.val = ∑ i : Fin N, a₁ i) := by
  classical
  have _hJ := hJ
  let := Fintype.ofFinite S.D
  let z := additiveParameter F q r
  let T := centerCompactTrivialization F ζ hζ q S.heisenberg S.borel S.iwasawa .plus z
  let a := T f.val
  obtain ⟨m,g,E,hE,hB,hdis,hcover,hcell,hc⟩ := actual_translated_cell_clopen_partition F ζ hζ q S
  have hcuts := fun i : Fin m => cell_cut_section F ζ hζ q S z a
    (g i) (E i) (hE i) (hB i) (hcell i) (hc i)
  choose v hv hvc hvzero using hcuts
  have hex := fun i : Fin m => actual_cell_finite_center_coordinate_expansion F ζ hζ q S P
    rep hrep r (v i) (hvc i) (hvzero i)
  choose φ hφ hcφ hφv using hex
  have hsum : (Set.toFinite (Set.univ : Set S.D)).toFinset = Finset.univ := by ext; simp
  simp only [hsum] at hφv
  let N := Fintype.card (Fin m × S.D)
  let e : Fin N ≃ Fin m × S.D := (Fintype.equivFin _).symm
  let gg := fun j : Fin N => g (e j).1
  let dd := fun j : Fin N => (e j).2
  let pp := fun j : Fin N => φ (e j).1 (e j).2
  let hp := fun j : Fin N => hφ (e j).1 (e j).2
  let hcp := fun j : Fin N => hcφ (e j).1 (e j).2
  obtain ⟨J₀,L,hL,hJ₀,hconj,ha₀,ha₁⟩ :=
    actual_pure_sections_individual_and_translated_levels F ζ hζ q S P J gg rep hrep dd pp hp hcp r
  refine ⟨N,gg,dd,pp,hp,hcp,J₀,L,hL,hJ₀,hconj,ha₀,ha₁,?_⟩
  apply T.injective
  rw [map_sum]
  simp only [T, z, LinearEquiv.apply_symm_apply]
  change a = ∑ j : Fin N, centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus z
    (gg j) (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
      rep hrep (dd j) (pp j) (hp j) (hcp j) r)
  have he := e.sum_comp (fun jd : Fin m × S.D =>
    centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus z (g jd.1)
      (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep jd.2 (φ jd.1 jd.2) (hφ jd.1 jd.2) (hcφ jd.1 jd.2) r))
  rw [show (∑ j : Fin N, _) = ∑ jd : Fin m × S.D,
      centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus z (g jd.1)
      (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep jd.2 (φ jd.1 jd.2) (hφ jd.1 jd.2) (hcφ jd.1 jd.2) r) from he]
  rw [Fintype.sum_prod_type]
  have hr : ∀ i : Fin m, (∑ d : S.D, centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus z
      (g i) (actualSection F ζ hζ q S.heisenberg S.borel P (S.openCell P)
        rep hrep d (φ i d) (hφ i d) (hcφ i d) r)) =
      centerPrincipalSeries F ζ hζ q S.heisenberg S.borel .plus z (g i) (v i) := by
    intro i
    rw [← map_sum, ← hφv i]
  simp_rw [hr]
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply]
  change a.val x = ∑ i : Fin m, (v i).val (x*g i)
  simp_rw [hv]
  simp only [mul_inv_cancel_right]
  obtain ⟨i,hi⟩ : ∃ i : Fin m, x ∈ E i := by
    have hx : x ∈ ⋃ i, E i := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hx
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    have hjx : x ∉ E j := fun h => Set.disjoint_left.mp (hdis hji) h hi
    simp [hjx]
  · simp

end

end DedekindZetaZeroFree.KPActualResidueSources
