module

public import DedekindZetaZeroFree.Adeles.Quotients.CompactOpenLevelTori

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical ContDiff
open NumberField IsDedekindDomain

abbrev SmoothAdeleQuotient (F : Type*) [Field F] [NumberField F] :=
  AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F

abbrev SmoothLevelTorus {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) :=
  mixedEmbedding.mixedSpace F ⧸ (finiteLevelLattice K).toAddSubgroup

def smoothArchInclusion (F : Type*) [Field F] [NumberField F]
    (x : mixedEmbedding.mixedSpace F) : SmoothAdeleQuotient F :=
  QuotientAddGroup.mk (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0) :
    AdeleRing (𝓞 F) F)

def HasSmoothAdditiveLevel {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (f : SmoothAdeleQuotient F → ℂ) : Prop :=
  ∀ (q : SmoothAdeleQuotient F) (h : finiteLevelImage K), f (q + h) = f q

def smoothLevelPullback {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (f : SmoothAdeleQuotient F → ℂ) (t : SmoothLevelTorus K) : ℂ :=
  f (smoothArchInclusion F (Quotient.out t))

def smoothArchJet {F : Type*} [Field F] [NumberField F]
    (n : ℕ) (f : SmoothAdeleQuotient F → ℂ) (q : SmoothAdeleQuotient F) :=
  iteratedFDeriv ℝ n (fun x : mixedEmbedding.mixedSpace F =>
    f (q + smoothArchInclusion F x)) 0

def IsArchSmooth {F : Type*} [Field F] [NumberField F]
    (f : SmoothAdeleQuotient F → ℂ) : Prop :=
  Continuous f ∧
    (∀ q, ContDiff ℝ ∞ (fun x : mixedEmbedding.mixedSpace F =>
      f (q + smoothArchInclusion F x))) ∧
    ∀ n : ℕ, Continuous (smoothArchJet n f)

def IsLevelTorusSmooth {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (g : SmoothLevelTorus K → ℂ) : Prop :=
  ContDiff ℝ ∞ (fun x : mixedEmbedding.mixedSpace F => g (QuotientAddGroup.mk x))

private theorem smoothArchInclusion_add {F : Type*} [Field F] [NumberField F]
    (x y : mixedEmbedding.mixedSpace F) :
    smoothArchInclusion F (x + y) = smoothArchInclusion F x + smoothArchInclusion F y := by
  let i : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F :=
    { toFun := fun x => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0)
      map_zero' := by change (_, _) = ((0, 0) : InfiniteAdeleRing F × _); simp
      map_add' := by
        intros a b
        change ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a + b),
          (0 : FiniteAdeleRing (𝓞 F) F)) =
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a +
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm b, 0 + 0)
        simp only [map_add, add_zero] }
  exact (((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)).comp i).map_add x y)

private theorem smoothArchInclusion_lattice {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (x : mixedEmbedding.mixedSpace F) (hx : x ∈ finiteLevelLattice K) :
    smoothArchInclusion F x ∈ finiteLevelImage K := by
  obtain ⟨a, ha, rfl⟩ := (mem_finiteLevelLattice_iff K x).mp hx
  refine ⟨-algebraMap F (FiniteAdeleRing (𝓞 F) F) a, K.neg_mem ha, ?_⟩
  change QuotientAddGroup.mk ((0, -algebraMap F (FiniteAdeleRing (𝓞 F) F) a) :
      AdeleRing (𝓞 F) F) = smoothArchInclusion F (mixedEmbedding F a)
  apply (QuotientAddGroup.eq_iff_sub_mem
    (G := AdeleRing (𝓞 F) F) (N := AdeleRing.principalSubgroup (𝓞 F) F)).mpr
  refine ⟨-a, ?_⟩
  change (algebraMap F (InfiniteAdeleRing F) (-a),
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (-a)) =
    (0 - (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (mixedEmbedding F a),
      -algebraMap F (FiniteAdeleRing (𝓞 F) F) a - 0)
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  simp only [map_neg, RingEquiv.symm_apply_apply, zero_sub, sub_zero]

private theorem smoothLevel_periodic {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (f : SmoothAdeleQuotient F → ℂ) (hf : HasSmoothAdditiveLevel K f)
    (x y : mixedEmbedding.mixedSpace F)
    (hxy : (QuotientAddGroup.mk x : SmoothLevelTorus K) = QuotientAddGroup.mk y) :
    f (smoothArchInclusion F x) = f (smoothArchInclusion F y) := by
  have hmem := smoothArchInclusion_lattice K (x - y)
    (QuotientAddGroup.eq_iff_sub_mem.mp hxy)
  have heq := hf (smoothArchInclusion F y) ⟨smoothArchInclusion F (x - y), hmem⟩
  simpa only [← smoothArchInclusion_add, add_sub_cancel] using heq

theorem smoothLevelPullback_mk {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (f : SmoothAdeleQuotient F → ℂ) (hf : HasSmoothAdditiveLevel K f)
    (x : mixedEmbedding.mixedSpace F) :
    smoothLevelPullback K f (QuotientAddGroup.mk x) = f (smoothArchInclusion F x) := by
  exact smoothLevel_periodic K f hf _ x (Quotient.out_eq _)

private theorem smooth_level_eq {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) {Y : Type*}
    (f : SmoothAdeleQuotient F → Y)
    (hf : ∀ q (h : finiteLevelImage K), f (q + h) = f q)
    {q r : SmoothAdeleQuotient F}
    (hqr : (QuotientAddGroup.mk q : finiteLevelAdditiveQuotient K) =
      QuotientAddGroup.mk r) : f q = f r := by
  have hm := QuotientAddGroup.eq_iff_sub_mem.mp hqr
  simpa only [add_sub_cancel] using hf r ⟨q - r, hm⟩

private theorem smooth_level_representative {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (q : SmoothAdeleQuotient F) :
    ∃ x : mixedEmbedding.mixedSpace F,
      (QuotientAddGroup.mk q : finiteLevelAdditiveQuotient K) =
        QuotientAddGroup.mk (smoothArchInclusion F x) := by
  obtain ⟨e, he⟩ := finiteLevel_torus_homeomorph K hcompact hopen
  obtain ⟨t, ht⟩ := e.surjective (QuotientAddGroup.mk q)
  induction t using QuotientAddGroup.induction_on with
  | H x => exact ⟨x, ht.symm.trans (he x)⟩

private theorem smooth_archJet_level {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (f : SmoothAdeleQuotient F → ℂ) (hf : HasSmoothAdditiveLevel K f) (n : ℕ) :
    ∀ q (h : finiteLevelImage K), smoothArchJet n f (q + h) = smoothArchJet n f q := by
  intro q h
  unfold smoothArchJet
  congr 1
  funext x
  simpa only [add_assoc, add_comm (h : SmoothAdeleQuotient F) (smoothArchInclusion F x)] using
    hf (q + smoothArchInclusion F x) h

private theorem smooth_family_continuous_iff {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    {P Y : Type*} [TopologicalSpace P] [TopologicalSpace Y]
    (f : P × SmoothAdeleQuotient F → Y)
    (hf : ∀ p q (h : finiteLevelImage K), f (p, q + h) = f (p, q)) :
    Continuous f ↔ Continuous (fun z : P × mixedEmbedding.mixedSpace F =>
      f (z.1, smoothArchInclusion F z.2)) := by
  obtain ⟨e, he⟩ := finiteLevel_torus_homeomorph K hcompact hopen
  let d : P × finiteLevelAdditiveQuotient K → Y :=
    fun z => f (z.1, Quotient.out z.2)
  have hd (p : P) (q : SmoothAdeleQuotient F) :
      d (p, QuotientAddGroup.mk q) = f (p, q) :=
    smooth_level_eq K (fun q => f (p, q)) (hf p) (Quotient.out_eq _)
  have hdE (p : P) (x : mixedEmbedding.mixedSpace F) :
      d (p, e (QuotientAddGroup.mk x)) = f (p, smoothArchInclusion F x) := by
    rw [he x]; exact hd p _
  have hQ := (IsOpenQuotientMap.id (X := P)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk (N := finiteLevelImage K))
  have hE := (IsOpenQuotientMap.id (X := P)).prodMap
    (e.toHomeomorph.isOpenQuotientMap.comp
      (QuotientAddGroup.isOpenQuotientMap_mk
        (N := (finiteLevelLattice K).toAddSubgroup)))
  have h1 : Continuous f ↔ Continuous d := by
    have heq : d ∘ Prod.map id QuotientAddGroup.mk = f :=
      funext (fun z => hd z.1 z.2)
    rw [← hQ.continuous_comp_iff, heq]
  have heq : d ∘ Prod.map id (e.toHomeomorph ∘ QuotientAddGroup.mk) =
      (fun z => f (z.1, smoothArchInclusion F z.2)) :=
    funext (fun z => hdE z.1 z.2)
  rw [h1, ← hE.continuous_comp_iff, heq]

private theorem smooth_continuous_iff {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    {Y : Type*} [TopologicalSpace Y] (f : SmoothAdeleQuotient F → Y)
    (hf : ∀ q (h : finiteLevelImage K), f (q + h) = f q) :
    Continuous f ↔ Continuous (fun x => f (smoothArchInclusion F x)) := by
  have h := smooth_family_continuous_iff K hcompact hopen
    (P := Unit) (fun z => f z.2) (fun _ => hf)
  constructor
  · intro hc
    exact (h.mp (hc.comp continuous_snd)).comp ((continuous_const (y := ())).prodMk continuous_id)
  · intro hc
    exact (h.mpr (hc.comp continuous_snd)).comp ((continuous_const (y := ())).prodMk continuous_id)

private theorem smooth_archJet_inclusion {F : Type*} [Field F] [NumberField F]
    (f : SmoothAdeleQuotient F → ℂ) (n : ℕ) (x : mixedEmbedding.mixedSpace F) :
    smoothArchJet n f (smoothArchInclusion F x) =
      iteratedFDeriv ℝ n (fun x => f (smoothArchInclusion F x)) x := by
  unfold smoothArchJet
  simp_rw [← smoothArchInclusion_add]
  simpa only [add_zero] using iteratedFDeriv_comp_add_left n x
    (0 : mixedEmbedding.mixedSpace F) (f := fun x => f (smoothArchInclusion F x))

theorem finiteLevel_smooth_iff {F : Type*} [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (f : SmoothAdeleQuotient F → ℂ) (hf : HasSmoothAdditiveLevel K f) :
    IsArchSmooth f ↔ IsLevelTorusSmooth K (smoothLevelPullback K f) := by
  have hfun : (fun x : mixedEmbedding.mixedSpace F =>
      smoothLevelPullback K f (QuotientAddGroup.mk x)) =
      (fun x => f (smoothArchInclusion F x)) :=
    funext (smoothLevelPullback_mk K f hf)
  unfold IsLevelTorusSmooth
  rw [hfun]
  constructor
  · intro hs
    have h := hs.2.1 0
    simpa only [smoothArchInclusion, map_zero, zero_add] using h
  · intro hs
    refine ⟨(smooth_continuous_iff K hcompact hopen f hf).mpr hs.continuous, ?_, ?_⟩
    · intro q
      obtain ⟨a, ha⟩ := smooth_level_representative K hcompact hopen q
      have heq : (fun x : mixedEmbedding.mixedSpace F => f (q + smoothArchInclusion F x)) =
          (fun x => f (smoothArchInclusion F (a + x))) := by
        funext x
        rw [smoothArchInclusion_add]
        apply smooth_level_eq K f hf
        exact congrArg (fun t : finiteLevelAdditiveQuotient K =>
          t + QuotientAddGroup.mk (smoothArchInclusion F x)) ha
      rw [heq]
      exact hs.comp (contDiff_const.add contDiff_id)
    · intro n
      apply (smooth_continuous_iff K hcompact hopen (smoothArchJet n f)
        (smooth_archJet_level K f hf n)).mpr
      simpa only [smooth_archJet_inclusion] using
        hs.continuous_iteratedFDeriv (m := n) (by simp)

def IsUniformArchSmoothFamily {F : Type*} [Field F] [NumberField F]
    {P : Type*} [TopologicalSpace P]
    (f : P × SmoothAdeleQuotient F → ℂ)
    (B : (n : ℕ) → (Fin n → mixedEmbedding.mixedSpace F) → ℝ) : Prop :=
  Continuous f ∧
    (∀ p : P, IsArchSmooth (fun q => f (p, q))) ∧
    (∀ n : ℕ, Continuous (fun z : P × SmoothAdeleQuotient F =>
      smoothArchJet n (fun q => f (z.1, q)) z.2)) ∧
    ∀ (n : ℕ) (v : Fin n → mixedEmbedding.mixedSpace F)
      (p : P) (q : SmoothAdeleQuotient F),
      ‖smoothArchJet n (fun q' => f (p, q')) q v‖ ≤ B n v

end
end DedekindZetaZeroFree
