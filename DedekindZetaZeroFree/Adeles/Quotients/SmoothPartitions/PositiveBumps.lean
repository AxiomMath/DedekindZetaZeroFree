module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.CountableShrinkingCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualSectorPositiveBumps
open KPContActualCotangentCountableShrinking KPContSectorCoveredQuotientVocabulary
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

structure PositiveBumps {n : ℕ} (C : Fin n → ShrunkChart F ζ hζ U R P H) (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) where
  bump : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ
  continuous : ∀ i, Continuous (bump i)
  smooth : ∀ i (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ),
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => bump i (Quotient.mk _ (x,c)))
  nonnegative : ∀ i x, 0 ≤ bump i x
  compact_support : ∀ i, HasCompactSupport (bump i)
  support_subset : ∀ i, tsupport (bump i) ⊆ (C i).baseDomain ∩ O
  positive_sum : ∀ x ∈ K, 0 < ∑ i, bump i x
  lift : Fin n → SymmetricSpace F → ℝ
  lift_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (lift i)
  lift_compact_support : ∀ i, HasCompactSupport (lift i)
  lift_support_subset : ∀ i, tsupport (lift i) ⊆ (C i).domain
  lift_invariant : ∀ i (σ : (C i).Isotropy) x, lift i ((σ.val : KPCuspArithmetic.PGL2 F) • x) = lift i x
  lift_restriction : ∀ i (x : (C i).domain), lift i x.val = bump i ((C i).toBase x)
  lift_zero_outside : ∀ i x, x ∉ (C i).domain → lift i x = 0

namespace Construction
open KPContSectorPhaseComponentCharts

 def Q (C : ShrunkChart F ζ hζ U R P H) (x : SymmetricSpace F) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  Quotient.mk _ (x,(H.atlas U).representative C.component)
private theorem Q_cont (C : ShrunkChart F ζ hζ U R P H) : Continuous (Q C) :=
  continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)
private theorem act_smooth (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => γ • x) := by
  change ContDiff ℝ (⊤ : ℕ∞) (KPCuspSiegel.action F γ)
  unfold KPCuspSiegel.action KPCuspSiegel.glAction
  exact (KPArch.productAction_contDiff _ _).of_le (by simp)
private theorem Q_inv (C : ShrunkChart F ζ hζ U R P H) (σ : C.Isotropy) (x : SymmetricSpace F) :
    Q C ((σ.val : KPCuspArithmetic.PGL2 F) • x) = Q C x := by
  change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
    (KPCuspSiegel.projection F _ (σ.val • x)) =
    KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
      (KPCuspSiegel.projection F _ x)
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component))
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  exact MulAction.mem_orbit_iff.mpr ⟨σ.val,rfl⟩

private theorem upstairs (C : ShrunkChart F ζ hζ U R P H)
    (O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hO : IsOpen O)
    (y : C.domain) (hy : C.toBase y ∈ O) :
    ∃ b : SymmetricSpace F → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      tsupport b ⊆ C.domain ∩ Q C ⁻¹' O ∧ (∀ x, 0 ≤ b x) ∧ 0 < b y.val ∧
      ∀ (σ : C.Isotropy) x, b ((σ.val : KPCuspArithmetic.PGL2 F) • x) = b x := by
  let hp := every_shrunkChart_properties F ζ hζ U R P H C
  letI : Finite C.Isotropy := hp.finite_isotropy
  letI := Fintype.ofFinite C.Isotropy
  letI : ContinuousConstSMul (Component F ζ hζ U R P H C.component) (SymmetricSpace F) :=
    ⟨fun g => KPCuspSiegel.continuous_action F g.val⟩
  let W := C.domain ∩ Q C ⁻¹' O
  have hW : IsOpen W := C.domain_open.inter (hO.preimage (Q_cont C))
  have hyW : y.val ∈ W := ⟨y.property,hy⟩
  obtain ⟨f,hfs,hfc,hfd,hfr,hfy⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hW.mem_nhds hyW)
  let b : SymmetricSpace F → ℝ := fun x => ∑ σ : C.Isotropy, f ((σ.val : KPCuspArithmetic.PGL2 F) • x)
  have hfinv (σ : C.Isotropy) (x : SymmetricSpace F) :
      (σ.val : KPCuspArithmetic.PGL2 F) • x ∈ W ↔ x ∈ W := by
    have hdom : (σ.val : KPCuspArithmetic.PGL2 F) • x ∈ C.domain ↔ x ∈ C.domain := by
      constructor
      · intro hx
        have hh := Set.mem_image_of_mem (fun z : SymmetricSpace F => (σ.val⁻¹ : KPCuspArithmetic.PGL2 F) • z) hx
        have ht := C.invariant σ⁻¹
        have hh' : (σ.val⁻¹ : KPCuspArithmetic.PGL2 F) • ((σ.val : KPCuspArithmetic.PGL2 F) • x) ∈ C.domain :=
          (congrArg (fun S : Set (SymmetricSpace F) => _ ∈ S) ht).mp hh
        simpa using hh'
      · intro hx
        have hh := Set.mem_image_of_mem (fun z : SymmetricSpace F => (σ.val : KPCuspArithmetic.PGL2 F) • z) hx
        exact (congrArg (fun S : Set (SymmetricSpace F) => _ ∈ S) (C.invariant σ)).mp hh
    simp only [W, Set.mem_inter_iff,Set.mem_preimage,Q_inv,hdom]
  have hbc : HasCompactSupport b := by
    have hh (σ : C.Isotropy) : HasCompactSupport (fun x : SymmetricSpace F => f ((σ.val : KPCuspArithmetic.PGL2 F) • x)) :=
      hfc.comp_homeomorph (Homeomorph.smul σ.val)
    convert HasCompactSupport.finset_sum (s := Finset.univ) (fun σ _ => hh σ) using 1
    funext x; exact (Finset.sum_apply x (Finset.univ : Finset C.Isotropy)
      (fun σ (z : SymmetricSpace F) => f ((σ.val : KPCuspArithmetic.PGL2 F) • z))).symm
  have hbs : tsupport b ⊆ W := by
    have hfc' (σ : C.Isotropy) : tsupport (fun x : SymmetricSpace F => f ((σ.val : KPCuspArithmetic.PGL2 F) • x)) ⊆ W := by
      intro x hx
      exact (hfinv σ x).mp (hfs ((KPCuspSiegel.continuous_action F σ.val.val).closure_preimage_subset (Function.support f) hx))
    apply (show tsupport b ⊆ ⋃ σ : C.Isotropy, tsupport (fun x : SymmetricSpace F => f ((σ.val : KPCuspArithmetic.PGL2 F) • x)) from ?_).trans
      (Set.iUnion_subset hfc')
    apply closure_minimal
    · intro x hx
      by_contra hn
      have hz : ∀ σ : C.Isotropy, f ((σ.val : KPCuspArithmetic.PGL2 F) • x) = 0 := by
        intro σ; by_contra hh
        exact hn (Set.mem_iUnion.mpr ⟨σ,subset_tsupport _ hh⟩)
      exact hx (by simp [b,hz])
    · exact isClosed_iUnion_of_finite (fun _ => isClosed_tsupport _)
  refine ⟨b, ContDiff.sum (fun σ _ => hfd.comp (act_smooth σ.val.val)),hbc,hbs,?_,?_,?_⟩
  · intro x; exact Finset.sum_nonneg (fun σ _ => (hfr ⟨_,rfl⟩).1)
  · have hh := Finset.single_le_sum (s := Finset.univ) (a := (1 : C.Isotropy))
      (fun σ _ => (hfr ⟨(σ.val : KPCuspArithmetic.PGL2 F) • y.val,rfl⟩).1) (Finset.mem_univ 1)
    have ht : f (((1 : C.Isotropy).val : KPCuspArithmetic.PGL2 F) • y.val) = 1 := by simpa using hfy
    change 0 < ∑ σ : C.Isotropy, f ((σ.val : KPCuspArithmetic.PGL2 F) • y.val)
    linarith
  · intro σ x
    apply Fintype.sum_bijective (fun τ : C.Isotropy => τ*σ) (Group.mulRight_bijective σ)
    intro τ
    simp only [Subgroup.coe_mul,mul_smul]

private theorem descend (C : ShrunkChart F ζ hζ U R P H) (b : SymmetricSpace F → ℝ)
    (hb : Continuous b) (hc : HasCompactSupport b) (hs : tsupport b ⊆ C.domain)
    (hn : ∀ x, 0 ≤ b x)
    (hi : ∀ (σ : C.Isotropy) x, b ((σ.val : KPCuspArithmetic.PGL2 F) • x) = b x) :
    ∃ f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ,
      Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ Q C '' tsupport b ∧
      (∀ x, 0 ≤ f x) ∧ ∀ y : C.domain, f (C.toBase y) = b y.val := by
  let hp := every_shrunkChart_properties F ζ hζ U R P H C
  let lift : C.baseDomain → C.domain := fun x => x.property.choose
  have hl : ∀ x : C.baseDomain, C.toBase (lift x) = x.val := fun x => x.property.choose_spec
  let f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := fun x =>
    if hx : x ∈ C.baseDomain then b (lift ⟨x,hx⟩).val else 0
  have hformula : ∀ y : C.domain, f (C.toBase y) = b y.val := by
    intro y
    have hy : C.toBase y ∈ C.baseDomain := Set.mem_range_self y
    simp only [f,dif_pos hy]
    obtain ⟨σ,hσ⟩ := (hp.orbit_fibers (lift ⟨C.toBase y,hy⟩) y).mp (hl _)
    have hh := congrArg Subtype.val hσ
    exact (hi σ _).symm.trans (congrArg b hh)
  have him : IsCompact (Q C '' tsupport b) := hc.image (Q_cont C)
  have hsu : Function.support f ⊆ Q C '' tsupport b := by
    intro x hx
    by_cases hxB : x ∈ C.baseDomain
    · refine ⟨(lift ⟨x,hxB⟩).val,?_,hl _⟩
      exact subset_tsupport _ (by simpa [f,hxB] using hx)
    · exact (hx (by simp [f,hxB])).elim
  have hts : tsupport f ⊆ Q C '' tsupport b := closure_minimal hsu him.isClosed
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxB : x ∈ C.baseDomain
    · have hr : Continuous (fun y : C.baseDomain => f y.val) := by
        apply hp.quotient.continuous_iff.mpr
        have he : (fun y : C.baseDomain => f y.val) ∘ C.quotientMap = b ∘ Subtype.val := by
          funext y; exact hformula y
        rw [he]
        exact hb.comp continuous_subtype_val
      exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hp.base_open.mem_nhds hxB)
    · have hxS : x ∉ Q C '' tsupport b := by
        rintro ⟨y,hy,rfl⟩
        exact hxB ⟨⟨y,hs hy⟩,rfl⟩
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [him.isClosed.isOpen_compl.mem_nhds hxS] with z hz
      exact image_eq_zero_of_notMem_tsupport (fun ht => hz (hts ht))
  refine ⟨f,hf,him.of_isClosed_subset (isClosed_tsupport _) hts,hts,?_,hformula⟩
  intro x
  simp only [f]
  split_ifs
  · exact hn _
  · exact le_rfl

private theorem descend_smooth (C : ShrunkChart F ζ hζ U R P H)
    (b : SymmetricSpace F → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hs : tsupport f ⊆ C.baseDomain)
    (hform : ∀ y : C.domain, f (C.toBase y) = b y.val)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => f (Quotient.mk _ (x,c))) := by
  let q : SymmetricSpace F → KPFiniteCuspAtlas.rawXU F ζ hζ U := fun x => Quotient.mk _ (x,c)
  have hq : Continuous q := continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : q x ∈ tsupport f
  · obtain ⟨y,hy⟩ := hs hx
    change (Quotient.mk _ (y.val,(H.atlas U).representative C.component) : KPFiniteCuspAtlas.rawXU F ζ hζ U) =
      Quotient.mk _ (x,c) at hy
    obtain ⟨γ,ε,u,hxγ,hc⟩ := Quotient.exact hy
    change x = γ • y.val at hxγ
    have hxD : γ⁻¹ • x ∈ C.domain := by rw [hxγ]; simpa using y.property
    have ha := act_smooth (F := F) γ⁻¹
    apply (hb.contDiffAt.comp x ha.contDiffAt).congr_of_eventuallyEq
    have hnh : (fun z : SymmetricSpace F => γ⁻¹ • z) ⁻¹' C.domain ∈ 𝓝 x :=
      (C.domain_open.preimage ha.continuous).mem_nhds hxD
    filter_upwards [hnh] with z hz
    have he : (Quotient.mk _ (γ⁻¹ • z,(H.atlas U).representative C.component) : KPFiniteCuspAtlas.rawXU F ζ hζ U) =
        Quotient.mk _ (z,c) := by
      apply Quotient.sound
      exact ⟨γ,ε,u,by simp,hc⟩
    change f (Quotient.mk _ (z,c)) = b (γ⁻¹ • z)
    rw [← he]
    exact hform ⟨γ⁻¹ • z,hz⟩
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hq.continuousAt.preimage_mem_nhds ((isClosed_tsupport f).isOpen_compl.mem_nhds hx)] with z hz
    exact image_eq_zero_of_notMem_tsupport hz

private theorem point_bump (C : ShrunkChart F ζ hζ U R P H)
    (O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hO : IsOpen O)
    (x : KPFiniteCuspAtlas.rawXU F ζ hζ U) (hx : x ∈ C.baseDomain ∩ O) :
    ∃ (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) (b : SymmetricSpace F → ℝ),
      Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ C.baseDomain ∩ O ∧
      (∀ c : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
        ContDiff ℝ (⊤ : ℕ∞) (fun z : SymmetricSpace F => f (Quotient.mk _ (z,c)))) ∧
      (∀ z,0 ≤ f z) ∧ 0 < f x ∧ ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      tsupport b ⊆ C.domain ∧
      (∀ (σ : C.Isotropy) z, b ((σ.val : KPCuspArithmetic.PGL2 F) • z) = b z) ∧
      (∀ y : C.domain,f (C.toBase y) = b y.val) ∧
      (∀ z,z ∉ C.domain → b z = 0) := by
  obtain ⟨y,rfl⟩ := hx.1
  obtain ⟨b,hb,hbc,hbs,hbn,hby,hbi⟩ := upstairs C O hO y hx.2
  obtain ⟨f,hf,hfc,hfs,hfn,hform⟩ := descend C b hb.continuous hbc (fun z hz => (hbs hz).1) hbn hbi
  have hts : tsupport f ⊆ C.baseDomain ∩ O := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := hfs hz
    exact ⟨⟨⟨w,(hbs hw).1⟩,rfl⟩,(hbs hw).2⟩
  refine ⟨f,b,hf,hfc,hts,descend_smooth C b hb f (fun z hz => (hts hz).1) hform,hfn,?_,hb,hbc,
    (fun z hz => (hbs hz).1),hbi,hform,?_⟩
  · rw [hform]; exact hby
  · intro z hz
    exact image_eq_zero_of_notMem_tsupport (fun hh => hz (hbs hh).1)

private theorem sum_tsupport {X : Type*} [TopologicalSpace X] {ι : Type*}
    (s : Finset ι) (f : ι → X → ℝ) : tsupport (fun x => ∑ j ∈ s, f j x) ⊆
      ⋃ j ∈ s, tsupport (f j) := by
  apply closure_minimal
  · intro x hx
    by_contra hn
    have hz : ∀ j ∈ s, f j x = 0 := by
      intro j hj
      by_contra hh
      exact hn (Set.mem_iUnion₂.mpr ⟨j,hj,subset_tsupport _ hh⟩)
    exact hx (Finset.sum_eq_zero hz)
  · exact isClosed_biUnion_finset (fun _ _ => isClosed_tsupport _)

private theorem produce {n : ℕ} (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) (hcover : K ⊆ ⋃ i, (C i).baseDomain) :
    Nonempty (PositiveBumps C K O) := by
  classical
  have hidx : ∀ x : K, ∃ i : Fin n, x.val ∈ (C i).baseDomain ∩ O := by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover x.property)
    exact ⟨i,hi,hKO x.property⟩
  choose idx hidx using hidx
  choose f b hfc hfcomp hfsub hfsm hfn hfpos hbsm hbcomp hbsub hbinv hform hbzero using
    (fun x : K => point_bump (C (idx x)) O hO x.val (hidx x))
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x : K => {z | 0 < f x z})
    (fun x => isOpen_lt continuous_const (hfc x)) (by
      intro x hx; exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hfpos _⟩)
  let t : Fin n → Finset K := fun i => s.filter (fun x => idx x = i)
  let fs : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := fun i z => ∑ x ∈ t i, f x z
  let B : Fin n → SymmetricSpace F → ℝ := fun i z => ∑ x ∈ t i, b x z
  have hidx' (i : Fin n) (x : K) (hx : x ∈ t i) : idx x = i := (Finset.mem_filter.mp hx).2
  have hsub (i : Fin n) : tsupport (fs i) ⊆ (C i).baseDomain ∩ O := by
    apply (sum_tsupport (t i) f).trans
    exact Set.iUnion₂_subset (fun x hx => by simpa [hidx' i x hx] using hfsub x)
  have hbsub' (i : Fin n) : tsupport (B i) ⊆ (C i).domain := by
    apply (sum_tsupport (t i) b).trans
    exact Set.iUnion₂_subset (fun x hx => by simpa [hidx' i x hx] using hbsub x)
  refine ⟨{ bump := fs
            continuous := fun i => continuous_finset_sum _ (fun x _ => hfc x)
            smooth := fun i c => ContDiff.sum (fun x _ => hfsm x c)
            nonnegative := fun i z => Finset.sum_nonneg (fun x _ => hfn x z)
            compact_support := ?_
            support_subset := hsub
            positive_sum := ?_
            lift := B
            lift_smooth := fun i => ContDiff.sum (fun x _ => hbsm x)
            lift_compact_support := ?_
            lift_support_subset := hbsub'
            lift_invariant := ?_
            lift_restriction := ?_
            lift_zero_outside := ?_ }⟩
  · intro i
    convert HasCompactSupport.finset_sum (s := t i) (fun x _ => hfcomp x) using 1
    funext z
    exact (Finset.sum_apply z (t i) f).symm
  · intro z hz
    obtain ⟨x,hxs,hxz⟩ := Set.mem_iUnion₂.mp (hs hz)
    have hxt : x ∈ t (idx x) := by simp [t,hxs]
    have h1 : f x z ≤ fs (idx x) z :=
      Finset.single_le_sum (fun y _ => hfn y z) hxt
    have h2 : fs (idx x) z ≤ ∑ i, fs i z :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun y _ => hfn y z)) (Finset.mem_univ _)
    exact hxz.trans_le (h1.trans h2)
  · intro i
    convert HasCompactSupport.finset_sum (s := t i) (fun x _ => hbcomp x) using 1
    funext z
    exact (Finset.sum_apply z (t i) b).symm
  · intro i σ z
    apply Finset.sum_congr rfl
    intro x hx
    have he := hidx' i x hx
    subst i
    exact hbinv x σ z
  · intro i y
    apply Finset.sum_congr rfl
    intro x hx
    have he := hidx' i x hx
    subst i
    exact (hform x y).symm
  · intro i z hz
    exact image_eq_zero_of_notMem_tsupport (fun hh => hz (hbsub' i hh))

end Construction

theorem actual_positive_bumps
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (n : ℕ) (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hcover : K ⊆ ⋃ i, (C i).baseDomain) : Nonempty (PositiveBumps C K O) := by
  exact Construction.produce C K O hK hO hKO hcover

end DedekindZetaZeroFree.KPContActualSectorPositiveBumps

end
