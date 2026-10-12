module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.MeasurableFamilies
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.InverseTransportCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentExactMeasurableGluing

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking KPContActualCotangentBorelRefinement
open KPContActualCotangentBorelOverlapDescent KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContActualCotangentTransportChoiceAlgebra
open KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

abbrev SequenceFields (cover : CountableCover F ζ hζ U R P H) :=
  ∀ n : ℕ, omega (cover.chart n) → E F

def ambientSequence (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (n : ℕ) (x : M F) : E F :=
  if hx : x ∈ omega (cover.chart n) then f n ⟨x, hx⟩ else 0

def IsPieceSequence (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) : Prop :=
  (∀ n, Measurable (f n)) ∧
  (∀ n (y : omega (cover.chart n)),
    q (cover.chart n) y.val ∉ basePiece cover n → f n y = 0) ∧
  EquivariantSequence cover (ambientSequence cover f)

 lemma ambientSequence_zero (cover : CountableCover F ζ hζ U R P H) :
    ambientSequence cover (0 : SequenceFields cover) = fun _ _ => (0 : E F) := by
  funext n x
  by_cases hx : x ∈ omega (cover.chart n) <;> simp [ambientSequence, hx]

 lemma ambientSequence_add (cover : CountableCover F ζ hζ U R P H)
    (f g : SequenceFields cover) :
    ambientSequence cover (f + g) = ambientSequence cover f + ambientSequence cover g := by
  funext n x
  by_cases hx : x ∈ omega (cover.chart n) <;> simp [ambientSequence, hx]

 lemma ambientSequence_smul (cover : CountableCover F ζ hζ U R P H)
    (c : ℂ) (f : SequenceFields cover) :
    ambientSequence cover (c • f) = c • ambientSequence cover f := by
  funext n x
  by_cases hx : x ∈ omega (cover.chart n) <;> simp [ambientSequence, hx]

def pieceSequenceSubmodule (cover : CountableCover F ζ hζ U R P H) :
    Submodule ℂ (SequenceFields cover) where
  carrier := {f | IsPieceSequence cover f}
  zero_mem' := by
    refine ⟨fun n => measurable_zero, fun n y hy => rfl, ?_⟩
    rw [ambientSequence_zero]
    intro n γ y hy
    simp
  add_mem' := fun {f g} hf hg => by
    obtain ⟨hf1, hf2, hf3⟩ := hf
    obtain ⟨hg1, hg2, hg3⟩ := hg
    refine ⟨fun n => (hf1 n).add (hg1 n), ?_, ?_⟩
    · intro n y hy
      simp only [Pi.add_apply]
      rw [hf2 n y hy, hg2 n y hy, add_zero]
    · rw [ambientSequence_add]
      intro n γ y hy
      simp only [Pi.add_apply]
      rw [hf3 n γ y hy, hg3 n γ y hy, map_add]
  smul_mem' := fun c {f} hf => by
    obtain ⟨hf1, hf2, hf3⟩ := hf
    refine ⟨fun n => (hf1 n).const_smul c, ?_, ?_⟩
    · intro n y hy
      simp only [Pi.smul_apply]
      rw [hf2 n y hy, smul_zero]
    · rw [ambientSequence_smul]
      intro n γ y hy
      simp only [Pi.smul_apply]
      rw [hf3 n γ y hy, map_smul]

abbrev PieceSequence (cover : CountableCover F ζ hζ U R P H) :=
  ↥(pieceSequenceSubmodule cover)

def enumeration (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (n : ℕ) :
    KPContCotangentCorrectedNullEquivalence.NonsingularEnumeration2 a (cover.chart n) :=
  Classical.choice ((kp_cont_actual_cotangent_borel_overlap_descent
    F ζ hζ R.adelicHaar R.adelic_isHaar U R rfl P H cover ℂ a).1 n)

def cell (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (n k : ℕ) : Set (M F) :=
  q a ⁻¹' basePiece cover n ∩
    disjointed (fun j => ((enumeration cover a n).branch j).domain) k

theorem cell_subset_domain (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (n k : ℕ) :
    cell cover a n k ⊆ ((enumeration cover a n).branch k).domain := by
  intro x hx
  exact disjointed_subset (fun j => ((enumeration cover a n).branch j).domain) k hx.2

theorem cell_subset_omega (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (n k : ℕ) :
    cell cover a n k ⊆ omega a := by
  exact (cell_subset_domain cover a n k).trans
    ((enumeration cover a n).properties k).source_subset

structure PartitionProperties (cover : CountableCover F ζ hζ U R P H) : Prop where
  measurable : ∀ a n k, MeasurableSet (cell cover a n k)
  disjoint : ∀ a, Pairwise (fun i j : ℕ × ℕ =>
    Disjoint (cell cover a i.1 i.2) (cell cover a j.1 j.2))
  covers : ∀ a, (⋃ i : ℕ × ℕ, cell cover a i.1 i.2) = omega a

 lemma continuous_labeledA_placeEquiv :
    Continuous (labeledA (placeEquiv F ζ hζ)) := by
  apply continuous_pi
  intro k
  exact (continuous_apply _).comp (CotangentLogCoframe.A (d F)).continuous

private lemma measurable_q (a : ShrunkChart F ζ hζ U R P H) : Measurable (q a) := by
  have hcm : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U
      ((H.atlas U).representative a.component)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component) =
        (H.atlas U).components ∘ Sigma.mk a.component := by
      funext x; exact ((H.atlas U).components_formula a.component x).symm
    rw [he]
    exact ((H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk).continuous
  have hproj : Measurable (KPCuspSiegel.projection F
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)) :=
    measurable_quotient_mk''
  have hcomp : q a = KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative a.component)
      ∘ KPCuspSiegel.projection F (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H a.component)
      ∘ labeledA (placeEquiv F ζ hζ) := rfl
  rw [hcomp]
  exact hcm.measurable.comp (hproj.comp continuous_labeledA_placeEquiv.measurable)

theorem partition_properties (cover : CountableCover F ζ hζ U R P H) :
    PartitionProperties cover := by
  classical
  have hbase := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  refine ⟨?_, ?_, ?_⟩
  · intro a n k
    exact ((measurable_q a) (hbase.base_measurable n)).inter
      (MeasurableSet.disjointed
        (fun j => ((enumeration cover a n).properties j).source_open.measurableSet) k)
  · intro a i j hij
    by_cases hn : i.1 = j.1
    · rw [hn]
      by_cases hk : i.2 = j.2
      · exact absurd (Prod.ext hn hk) hij
      · refine Disjoint.mono Set.inter_subset_right Set.inter_subset_right ?_
        exact disjoint_disjointed
          (fun k => ((enumeration cover a j.1).branch k).domain) hk
    · refine Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_
      exact Disjoint.preimage (q a) (hbase.pairwise_disjoint hn)
  · intro a
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact cell_subset_omega cover a i.1 i.2 hi
    · intro x hx
      have hxmem : q a x ∈ ⋃ n, basePiece cover n := by
        rw [hbase.covers]; exact Set.mem_univ _
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxmem
      have hcov : x ∈ ⋃ k, ((enumeration cover a n).branch k).domain := by
        rw [(enumeration cover a n).covers]
        exact ⟨hx, hbase.base_subset n hn⟩
      have hcov' : x ∈ ⋃ k,
          disjointed (fun j => ((enumeration cover a n).branch j).domain) k := by
        rwa [iUnion_disjointed]
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hcov'
      exact Set.mem_iUnion.mpr ⟨(n, k), hn, hk⟩

private lemma T_apply_twisted {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (v : E F) :
    T ψ x hx v = twistedOperator ψ x v :=
  congrArg (fun (f : E F →L[ℂ] E F) => f v) (T_toContinuousLinearMap ψ x hx)

private lemma T_congr {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (h1 h2 : x ∈ ψ.domain) :
    T ψ x h1 = T ψ x h2 := by
  apply LinearIsometryEquiv.ext
  intro v
  rfl

private lemma T_symm_coord {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) i}
    (ψ : Arrow a b) (x : M F) (hx : x ∈ ψ.domain) (w : E F)
    (k : Fin (d F) × Fin 3) :
    (T ψ x hx).symm w k =
      inner ℂ (twistedOperator ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)) w := by
  have hb : T ψ x hx (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)
      = twistedOperator ψ x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k) :=
    T_apply_twisted ψ x hx _
  have h1 : (T ψ x hx).symm w k
      = inner ℂ ((EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k)) ((T ψ x hx).symm w) := by
    simpa using (EuclideanSpace.basisFun_inner (ι := Fin (d F) × Fin 3) (𝕜 := ℂ)
      ((T ψ x hx).symm w) k).symm
  rw [h1, ← inner_conj_symm]
  conv_lhs =>
    rw [← (T ψ x hx).symm_apply_apply (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k),
      LinearIsometryEquiv.inner_map_map (T ψ x hx).symm w
        (T ψ x hx (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℂ k))]
  rw [inner_conj_symm, hb]

private lemma measurable_ambientSequence (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (hf : IsPieceSequence cover f) (n : ℕ) :
    Measurable (ambientSequence cover f n) := by
  have hω : MeasurableSet (omega (cover.chart n)) := by
    rw [KPContCotangentOverlapRationalBranches.omega]
    exact ((continuous_labeledA_placeEquiv (F := F) (ζ := ζ) (hζ := hζ)).isOpen_preimage _
      (cover.chart n).domain_open).measurableSet
  exact Measurable.dite (hf.1 n) measurable_const hω

def cellIndex (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (x : omega a) : ℕ × ℕ :=
  Classical.choose (show ∃ i : ℕ × ℕ, x.val ∈ cell cover a i.1 i.2 from by
    have hx : x.val ∈ ⋃ i : ℕ × ℕ, cell cover a i.1 i.2 := by
      rw [(partition_properties cover).covers a]
      exact x.property
    exact Set.mem_iUnion.mp hx)

theorem cellIndex_mem (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (x : omega a) :
    x.val ∈ cell cover a (cellIndex cover a x).1 (cellIndex cover a x).2 := by
  classical
  unfold cellIndex
  exact Classical.choose_spec (show ∃ i : ℕ × ℕ, x.val ∈ cell cover a i.1 i.2 from by
    have hx : x.val ∈ ⋃ i : ℕ × ℕ, cell cover a i.1 i.2 := by
      rw [(partition_properties cover).covers a]
      exact x.property
    exact Set.mem_iUnion.mp hx)

def rawG (cover : CountableCover F ζ hζ U R P H) (f : SequenceFields cover) :
    ChartFields F ζ hζ U R P H := fun a x =>
  let i := cellIndex cover a x
  inverseTransport ((enumeration cover a i.1).branch i.2)
    (ambientSequence cover f i.1) x.val
    (cell_subset_domain cover a i.1 i.2 (cellIndex_mem cover a x))

private lemma rawG_cell (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (a : ShrunkChart F ζ hζ U R P H)
    (n k : ℕ) (x : omega a) (hx : x.val ∈ cell cover a n k) :
    rawG cover f a x = inverseTransport ((enumeration cover a n).branch k)
      (ambientSequence cover f n) x.val (cell_subset_domain cover a n k hx) := by
  have hi : cellIndex cover a x = (n, k) := by
    by_contra hne
    have hd := (partition_properties cover).disjoint a hne
    exact Set.disjoint_left.mp hd (cellIndex_mem cover a x) hx
  let v (i : ℕ × ℕ) : E F := if h : x.val ∈ cell cover a i.1 i.2 then
    inverseTransport ((enumeration cover a i.1).branch i.2)
      (ambientSequence cover f i.1) x.val (cell_subset_domain cover a i.1 i.2 h) else 0
  have hv : rawG cover f a x = v (cellIndex cover a x) := by
    simp only [v, dif_pos (cellIndex_mem cover a x)]
    rfl
  rw [hv, hi]
  exact (dif_pos hx)

private lemma measurable_inverseTransport (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (hf : IsPieceSequence cover f)
    (a : ShrunkChart F ζ hζ U R P H) (n k : ℕ) :
    Measurable (fun x : ((enumeration cover a n).branch k).domain =>
      inverseTransport ((enumeration cover a n).branch k)
        (ambientSequence cover f n) x.val x.property) := by
  let e := (enumeration cover a n).branch k
  have hp := (enumeration cover a n).properties k
  change Measurable (fun x : e.domain => inverseTransport e (ambientSequence cover f n) x.val x.property)
  cases he : e with
  | none =>
    change Measurable (fun x : (∅ : Set (M F)) => _)
    exact Subsingleton.measurable
  | some e' =>
    change Measurable (fun x : e'.arrow.domain =>
      (T e'.arrow x.val x.property).symm (ambientSequence cover f n (e'.arrow.psi x.val)))
    have hψ : Continuous (fun x : e'.arrow.domain => e'.arrow.psi x.val) := by
      have hs : ContinuousOn e.psi e.domain := hp.smooth.continuousOn
      rw [he] at hs
      exact continuousOn_iff_continuous_restrict.mp hs
    have ht : Continuous (fun x : e'.arrow.domain => twistedOperator e'.arrow x.val) :=
      continuousOn_iff_continuous_restrict.mp (smooth_operators e'.arrow).2.continuousOn
    suffices hm : Measurable (fun x : e'.arrow.domain =>
        WithLp.ofLp ((T e'.arrow x.val x.property).symm
          (ambientSequence cover f n (e'.arrow.psi x.val)))) from
      (WithLp.measurable_toLp 2 _).comp hm
    apply measurable_pi_iff.mpr
    intro j
    have hcoord : (fun x : e'.arrow.domain =>
        (T e'.arrow x.val x.property).symm (ambientSequence cover f n (e'.arrow.psi x.val)) j) =
        (fun x : e'.arrow.domain => inner ℂ
          (twistedOperator e'.arrow x.val (EuclideanSpace.basisFun _ ℂ j))
          (ambientSequence cover f n (e'.arrow.psi x.val))) := by
      funext x
      exact T_symm_coord e'.arrow x.val x.property _ j
    rw [hcoord]
    exact (ht.clm_apply continuous_const).measurable.inner
      ((measurable_ambientSequence cover f hf n).comp hψ.measurable)

private lemma measurable_rawG (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (hf : IsPieceSequence cover f)
    (a : ShrunkChart F ζ hζ U R P H) : Measurable (rawG cover f a) := by
  intro s hs
  have heq : (rawG cover f a) ⁻¹' s = ⋃ i : ℕ × ℕ,
      Subtype.val ⁻¹' cell cover a i.1 i.2 ∩ (rawG cover f a) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨cellIndex cover a x, cellIndex_mem cover a x, h⟩,
      fun ⟨_, _, h⟩ => h⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  let c : Set (omega a) := Subtype.val ⁻¹' cell cover a i.1 i.2
  have hc : MeasurableSet c := measurable_subtype_coe ((partition_properties cover).measurable a i.1 i.2)
  have hm : Measurable (fun x : c => rawG cover f a x.val) := by
    have hinc : Measurable (fun x : c =>
        (⟨x.val.val, cell_subset_domain cover a i.1 i.2 x.property⟩ :
          ((enumeration cover a i.1).branch i.2).domain)) :=
      (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
    have h := (measurable_inverseTransport cover f hf a i.1 i.2).comp hinc
    convert h using 1
    funext x
    exact rawG_cell cover f a i.1 i.2 x.val x.property
  have himg := MeasurableSet.subtype_image hc (hm hs)
  have hset : ((↑) : c → omega a) '' ((fun x : c => rawG cover f a x.val) ⁻¹' s) =
      c ∩ (rawG cover f a) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hsx⟩
      exact ⟨⟨x, hx⟩, hsx, rfl⟩
  rwa [hset] at himg

private lemma q_actualBranch {a b : ShrunkChart F ζ hζ U R P H}
    (e : ActualBranch a b) (x : M F) : q b (e.arrow.psi x) = q a x := by
  rcases a with ⟨i, ca, oa, da, dao, dac, das, dai⟩
  rcases b with ⟨j, cb, ob, db, dbo, dbc, dbs, dbi⟩
  rcases e with ⟨h, e, hs, ht, hl⟩
  dsimp at h
  subst j
  unfold KPContCotangentOverlapRationalBranches.q
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  simp only [Arrow.psi, coordinateMap, targetChart, isotropyChart,
    ChartKind.representative, inv_one, one_mul, mul_one]
  have ha (v : KPCuspGenuineMonodromy.SymmetricSpace F) :
      labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) v) = v := by
    funext k
    simp [labeledA, labeledAInv]
  rw [ha]
  apply Quotient.sound
  exact ⟨e.gamma, rfl⟩

private lemma cellIndex_fst (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (x : omega a) (n : ℕ)
    (hx : q a x.val ∈ basePiece cover n) : (cellIndex cover a x).1 = n := by
  by_contra hne
  have hb := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  exact Set.disjoint_left.mp (hb.pairwise_disjoint hne) (cellIndex_mem cover a x).1 hx

private lemma rawG_at_branch (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (hf : IsPieceSequence cover f)
    (a : ShrunkChart F ζ hζ U R P H) (n : ℕ)
    (e : Branch a (cover.chart n)) (x : omega a) (hx : x.val ∈ e.domain)
    (hn : q a x.val ∈ basePiece cover n) :
    rawG cover f a x = inverseTransport e (ambientSequence cover f n) x.val hx := by
  have hn' := cellIndex_fst cover a x n hn
  have hc : x.val ∈ cell cover a n (cellIndex cover a x).2 := by
    rw [← hn']; exact cellIndex_mem cover a x
  rw [rawG_cell cover f a n (cellIndex cover a x).2 x hc]
  exact (kp_cont_actual_cotangent_transport_choice_algebra F ζ hζ
    R.adelicHaar R.adelic_isHaar U R rfl P H cover _ hf.2.2).choice_independent
      a n _ e x.val _ hx

private lemma rawG_overlap (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (hf : IsPieceSequence cover f)
    (a b : ShrunkChart F ζ hζ U R P H) (e : ActualBranch a b)
    (x : M F) (hx : x ∈ e.arrow.domain) :
    rawG cover f b ⟨e.arrow.psi x, e.target_shrinking hx⟩ =
      T e.arrow x hx (rawG cover f a ⟨x, e.source_shrinking hx⟩) := by
  let y : omega b := ⟨e.arrow.psi x, e.target_shrinking hx⟩
  let j := cellIndex cover b y
  have hj := cellIndex_mem cover b y
  have hn : q a x ∈ basePiece cover j.1 := by
    rw [← q_actualBranch e x]
    exact hj.1
  let z : omega a := ⟨x, e.source_shrinking hx⟩
  have hz : (cellIndex cover a z).1 = j.1 := cellIndex_fst cover a z j.1 hn
  have hc : x ∈ cell cover a j.1 (cellIndex cover a z).2 := by
    rw [← hz]; exact cellIndex_mem cover a z
  rw [rawG_cell cover f a j.1 (cellIndex cover a z).2 z hc]
  change inverseTransport ((enumeration cover b j.1).branch j.2)
      (ambientSequence cover f j.1) (e.arrow.psi x) _ = _
  exact (kp_cont_actual_cotangent_transport_choice_algebra F ζ hζ
    R.adelicHaar R.adelic_isHaar U R rfl P H cover _ hf.2.2).mixed_charts
      a b j.1 (some e) _ _ x hx (cell_subset_domain cover a _ _ hc)
        (cell_subset_domain cover b _ _ hj)

 def isotropyBranch (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a) :
    ActualBranch a a where
  component_eq := rfl
  arrow := { isotropyArrow a γ with
    domain := omega a
    isOpen_domain := by
      exact (continuous_labeledA_placeEquiv.isOpen_preimage _ a.domain_open)
    source := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    target := fun x hx => (isotropyArrow a γ).target
      (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx) }
  source_shrinking := Set.Subset.refl _
  target_shrinking := fun x hx => isotropy_mem a γ x hx
  target_larger := fun x hx => (isotropyArrow a γ).target
    (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx)

theorem rawG_isMeasurableCotangentFamily
    (cover : CountableCover F ζ hζ U R P H) (f : SequenceFields cover)
    (hf : IsPieceSequence cover f) : IsMeasurableCotangentFamily (rawG cover f) := by
  refine ⟨measurable_rawG cover f hf, ?_, rawG_overlap cover f hf⟩
  intro a γ x hx
  have h := rawG_overlap cover f hf a a (isotropyBranch a γ) x hx
  convert h using 1
  · rfl
  · apply congrArg (fun t : E F ≃ₗᵢ[ℂ] E F => t (rawG cover f a ⟨x, hx⟩))
    apply LinearIsometryEquiv.ext
    intro v
    rfl

def G (cover : CountableCover F ζ hζ U R P H) (f : PieceSequence cover) :
    MeasurableCotangentFamily F ζ hζ U R P H :=
  ⟨rawG cover f.val, rawG_isMeasurableCotangentFamily cover f.val f.property⟩

 def identityBranch (a : ShrunkChart F ζ hζ U R P H) : ActualBranch a a where
  component_eq := rfl
  arrow := { KPContCotangentActualOverlap.identity (isotropyChart a) with
    domain := omega a
    isOpen_domain := continuous_labeledA_placeEquiv.isOpen_preimage _ a.domain_open
    source := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    target := by
      intro x hx
      change (KPContCotangentActualOverlap.identity (isotropyChart a)).psi x ∈ (isotropyChart a).omega
      rw [KPContCotangentActualGroupoidIdentities.identity_psi]
      exact KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx }
  source_shrinking := Set.Subset.refl _
  target_shrinking := by
    intro x hx
    change (KPContCotangentActualOverlap.identity (isotropyChart a)).psi x ∈ omega a
    rwa [KPContCotangentActualGroupoidIdentities.identity_psi]
  target_larger := by
    intro x hx
    change (KPContCotangentActualOverlap.identity (isotropyChart a)).psi x ∈ (isotropyChart a).omega
    rw [KPContCotangentActualGroupoidIdentities.identity_psi]
    exact KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx

private lemma rawG_on_piece (cover : CountableCover F ζ hζ U R P H)
    (f : SequenceFields cover) (hf : IsPieceSequence cover f) (n : ℕ)
    (y : omega (cover.chart n)) (hy : q (cover.chart n) y.val ∈ basePiece cover n) :
    rawG cover f (cover.chart n) y = f n y := by
  rw [rawG_at_branch cover f hf (cover.chart n) n (some (identityBranch (cover.chart n)))
    y y.property hy]
  have ht : T (identityBranch (cover.chart n)).arrow y.val y.property =
      LinearIsometryEquiv.refl ℂ (E F) := by
    apply LinearIsometryEquiv.ext
    intro v
    have h := congrArg (fun t : E F ≃ₗᵢ[ℂ] E F => t v)
      (T_identity (isotropyChart (cover.chart n)) y.val
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger _ y.property))
    exact h
  have hψ : (identityBranch (cover.chart n)).arrow.psi y.val = y.val :=
    congrFun (KPContCotangentActualGroupoidIdentities.identity_psi (isotropyChart (cover.chart n))) y.val
  simp only [inverseTransport, Branch.transport, Branch.psi, ht, hψ,
    ambientSequence, dif_pos y.property]
  rfl

structure Properties (cover : CountableCover F ζ hζ U R P H) : Prop where
  partition : PartitionProperties cover
  cell_formula : ∀ (f : PieceSequence cover)
    (a : ShrunkChart F ζ hζ U R P H) (n k : ℕ) (x : M F)
    (hx : x ∈ cell cover a n k),
    coefficient (G cover f) a ⟨x, cell_subset_omega cover a n k hx⟩ =
      inverseTransport ((enumeration cover a n).branch k)
        (ambientSequence cover f.val n) x (cell_subset_domain cover a n k hx)
  every_arrow : ∀ (f : PieceSequence cover)
    (a : ShrunkChart F ζ hζ U R P H) (n : ℕ)
    (ψ : ActualBranch a (cover.chart n)) (x : M F)
    (hx : x ∈ ψ.arrow.domain), q a x ∈ basePiece cover n →
    coefficient (G cover f) a ⟨x, ψ.source_shrinking hx⟩ =
      (T ψ.arrow x hx).symm (f.val n ⟨ψ.arrow.psi x, ψ.target_shrinking hx⟩)
  chart_measurable : ∀ (f : PieceSequence cover) a,
    Measurable (coefficient (G cover f) a)
  covariance : ∀ (f : PieceSequence cover)
    (a : ShrunkChart F ζ hζ U R P H) (γ : Gamma a) (x : M F)
    (hx : x ∈ omega a),
    coefficient (G cover f) a
        ⟨(isotropyArrow a γ).psi x, isotropy_mem a γ x hx⟩ =
      T (isotropyArrow a γ) x
        (KPContActualCotangentMeasurableFamilies.omega_subset_larger a hx)
        (coefficient (G cover f) a ⟨x, hx⟩)
  overlap : ∀ (f : PieceSequence cover)
    (a b : ShrunkChart F ζ hζ U R P H) (θ : ActualBranch a b) (x : M F)
    (hx : x ∈ θ.arrow.domain),
    coefficient (G cover f) b ⟨θ.arrow.psi x, θ.target_shrinking hx⟩ =
      T θ.arrow x hx (coefficient (G cover f) a ⟨x, θ.source_shrinking hx⟩)
  on_piece : ∀ (f : PieceSequence cover) (n : ℕ) (y : omega (cover.chart n)),
    q (cover.chart n) y.val ∈ basePiece cover n →
      coefficient (G cover f) (cover.chart n) y = f.val n y
  normSquare_on_piece : ∀ (f : PieceSequence cover) (n : ℕ)
    (y : omega (cover.chart n)), q (cover.chart n) y.val ∈ basePiece cover n →
      (normSquare (G cover f) (q (cover.chart n) y.val) : ℝ) = ‖f.val n y‖ ^ 2
  add : ∀ f g : PieceSequence cover, G cover (f + g) = G cover f + G cover g
  smul : ∀ (c : ℂ) (f : PieceSequence cover), G cover (c • f) = c • G cover f
  zero : G cover (0 : PieceSequence cover) = 0

private theorem properties (cover : CountableCover F ζ hζ U R P H) : Properties cover := by
  refine ⟨partition_properties cover, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f a n k x hx
    exact rawG_cell cover f.val a n k ⟨x, cell_subset_omega cover a n k hx⟩ hx
  · intro f a n ψ x hx hn
    have h := rawG_at_branch cover f.val f.property a n (some ψ)
      ⟨x, ψ.source_shrinking hx⟩ hx hn
    change rawG cover f.val a ⟨x, ψ.source_shrinking hx⟩ =
      (T ψ.arrow x hx).symm (f.val n ⟨ψ.arrow.psi x, ψ.target_shrinking hx⟩)
    rw [h]
    dsimp only [inverseTransport, Branch.transport, Branch.psi, ambientSequence]
    rw [dif_pos (ψ.target_shrinking hx)]
  · intro f a
    exact (G cover f).property.1 a
  · intro f a γ x hx
    exact (G cover f).property.2.1 a γ x hx
  · intro f a b θ x hx
    exact (G cover f).property.2.2 a b θ x hx
  · intro f n y hy
    exact rawG_on_piece cover f.val f.property n y hy
  · intro f n y hy
    rw [normSquare_chart]
    change (‖rawG cover f.val (cover.chart n) y‖₊ ^ 2 : ℝ) = _
    rw [rawG_on_piece cover f.val f.property n y hy]
    rfl
  · intro f g
    apply Subtype.ext
    funext a x
    change rawG cover (f.val + g.val) a x = rawG cover f.val a x + rawG cover g.val a x
    dsimp only [rawG]
    rw [ambientSequence_add]
    exact map_add _ _ _
  · intro c f
    apply Subtype.ext
    funext a x
    change rawG cover (c • f.val) a x = c • rawG cover f.val a x
    dsimp only [rawG]
    rw [ambientSequence_smul]
    dsimp only [inverseTransport, Pi.smul_apply]
    exact map_smul _ _ _
  · apply Subtype.ext
    funext a x
    change rawG cover (0 : SequenceFields cover) a x = 0
    dsimp only [rawG]
    rw [ambientSequence_zero]
    exact map_zero _

end DedekindZetaZeroFree.KPContActualCotangentExactMeasurableGluing

namespace DedekindZetaZeroFree

theorem kp_cont_actual_cotangent_exact_measurable_gluing
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : KPContActualCotangentCountableShrinking.CountableCover F ζ hζ U R P H) :
    KPContActualCotangentExactMeasurableGluing.Properties cover := by
  exact KPContActualCotangentExactMeasurableGluing.properties cover

end DedekindZetaZeroFree

end
