module

public import DedekindZetaZeroFree.Adeles.Lattices.CompactOpenLevelLattices
public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Archimedean.TraceNormalization

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

local instance finiteLevelCovolume_measurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

private theorem finiteLevelFieldSubgroup_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] :
    finiteLevelFieldSubgroup (integralFiniteAdeles F) = integerFieldSubgroup F := by
  ext lam
  rw [finiteLevelFieldSubgroup, AddSubgroup.mem_comap, integerFieldSubgroup,
    AddMonoidHom.mem_range]
  constructor
  · intro h
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F)
      lam ?_
    intro v
    have hv : ((algebraMap F (FiniteAdeleRing (𝓞 F) F) lam) v) ∈
        v.adicCompletionIntegers F := h v
    rw [FiniteAdeleRing.algebraMap_apply] at hv
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hv
  · rintro ⟨a, rfl⟩ v
    have hv : ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) F) a)) v) ∈
        v.adicCompletionIntegers F := by
      rw [FiniteAdeleRing.algebraMap_apply]
      exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a
    exact hv

private theorem finiteLevelLattice_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] :
    finiteLevelLattice (integralFiniteAdeles F) = NumberField.mixedEmbedding.integerLattice F := by
  ext x
  rw [mem_finiteLevelLattice_iff, NumberField.mixedEmbedding.integerLattice, LinearMap.mem_range]
  constructor
  · rintro ⟨lam, hmem, rfl⟩
    have h2 : lam ∈ integerFieldSubgroup F := by
      rw [← finiteLevelFieldSubgroup_integralFiniteAdeles F]
      exact hmem
    rw [integerFieldSubgroup, AddMonoidHom.mem_range] at h2
    obtain ⟨a, ha⟩ := h2
    refine ⟨a, ?_⟩
    show NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) = NumberField.mixedEmbedding F lam
    rw [← ha]
    rfl
  · rintro ⟨a, ha⟩
    refine ⟨algebraMap (𝓞 F) F a, ?_, ha⟩
    show (algebraMap (𝓞 F) F) a ∈ finiteLevelFieldSubgroup (integralFiniteAdeles F)
    rw [finiteLevelFieldSubgroup_integralFiniteAdeles F, integerFieldSubgroup,
      AddMonoidHom.mem_range]
    exact ⟨a, rfl⟩

set_option linter.style.haveILetI false in

private lemma ZLattice.covolume_smul_ofReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) :
    ZLattice.covolume L (ENNReal.ofReal c • μ) = c * ZLattice.covolume L μ := by
  have hc0 : (ENNReal.ofReal c) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
  have hctop : (ENNReal.ofReal c) ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : (ENNReal.ofReal c • μ).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ hc0 hctop
  have hac : (ENNReal.ofReal c • μ).AbsolutelyContinuous μ := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s _ hs
    rw [Measure.smul_apply, hs, smul_zero]
  let b := Module.Free.chooseBasis ℤ L
  have hfd : IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hfd' : IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ))
      (ENNReal.ofReal c • μ) := hfd.mono hac
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L _ hfd,
    ZLattice.covolume_eq_measure_fundamentalDomain L _ hfd',
    Measure.real_def, Measure.real_def, Measure.smul_apply]
  rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]

lemma finiteLevelCovolume_index_mul_measure
    {A : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    (μ : Measure A) [μ.IsAddLeftInvariant]
    (K H : AddSubgroup A) (hHK : H ≤ K)
    (hK : MeasurableSet (K : Set A)) (hH : MeasurableSet (H : Set A))
    [Finite (K ⧸ H.comap K.subtype)] :
    (Nat.card (K ⧸ H.comap K.subtype) : ENNReal) * μ (H : Set A) =
      μ (K : Set A) := by
  let ν : Measure K := μ.comap K.subtype
  have he : MeasurableEmbedding (K.subtype : K → A) :=
    MeasurableEmbedding.subtype_coe hK
  letI : MeasurableAdd K := ⟨fun k => (measurable_subtype_coe.const_add (k : A)).subtype_mk,
    fun k => (measurable_subtype_coe.add_const (k : A)).subtype_mk⟩
  letI : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ he
  let U := H.comap K.subtype
  letI : U.FiniteIndex := ⟨by change Nat.card (K ⧸ U) ≠ 0; exact Nat.card_pos.ne'⟩
  have hu : MeasurableSet (U : Set K) := hH.preimage measurable_subtype_coe
  have hmass := U.index_mul_measure hu ν
  have hHU : K.subtype '' (U : Set K) = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hHK hx⟩, hx, rfl⟩
  have hrange : Set.range (K.subtype : K → A) = K := Subtype.range_coe
  simpa only [AddSubgroup.index, ν, he.comap_apply μ, hHU,
    Set.image_univ, hrange] using hmass

theorem integralFiniteLevel_trace_covolume
    (F : Type) [Field F] [NumberField F] :
    ZLattice.covolume (finiteLevelLattice (integralFiniteAdeles F))
      (ENNReal.ofReal (PoissonArch.haarScalar F) • volume) =
        Real.sqrt |(NumberField.discr F : ℝ)| := by
  rw [finiteLevelLattice_integralFiniteAdeles F]
  rw [PoissonArch.haarScalar]
  rw [ZLattice.covolume_smul_ofReal _ volume (by positivity)]
  rw [NumberField.mixedEmbedding.covolume_integerLattice F]
  have h2 : (2:ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      ((2:ℝ)⁻¹) ^ NumberField.InfinitePlace.nrComplexPlaces F = 1 := by
    rw [← mul_pow]; norm_num
  rw [← mul_assoc, h2, one_mul]

private lemma integral_isCompact (F : Type) [Field F] [NumberField F] :
    IsCompact (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  convert KPAdelicTopology.integralAdeles_isCompact F using 1 <;> rfl
private lemma integral_isOpen (F : Type) [Field F] [NumberField F] :
    IsOpen (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  convert KPAdelicTopology.integralAdeles_isOpen F using 1 <;> rfl
private lemma scaled_topology (F : Type) [Field F] [NumberField F] (a : ℕ) (ha : 0 < a) :
    IsCompact (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) : Set (FiniteAdeleRing (𝓞 F) F)) ∧
    IsOpen (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) : Set (FiniteAdeleRing (𝓞 F) F)) := by
  let u : (FiniteAdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
    (Units.mk0 (a : F) (by exact_mod_cast ha.ne'))
  let e := ContinuousAddEquiv.mulLeft u
  have he : ⇑e = ⇑(integerScaleHom (a : ℤ) : FiniteAdeleRing (𝓞 F) F →+ _) := by
    ext x
    simp [e, u, integerScaleHom, zsmul_eq_mul]
  have hs : (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) : Set (FiniteAdeleRing (𝓞 F) F)) =
      e '' (integralFiniteAdeles F : Set _) := by
    rw [he]; rfl
  rw [hs]
  exact ⟨(integral_isCompact F).image e.continuous, e.toHomeomorph.isOpenMap _ (integral_isOpen F)⟩

private lemma mixed_covolume_ratio (F : Type) [Field F] [NumberField F]
    (L₁ L₂ : Submodule ℤ (mixedEmbedding.mixedSpace F))
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂]
    (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ volume / ZLattice.covolume L₂ volume =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
  let e := mixedEmbedding.euclidean.toMixed F
  have hr := ZLattice.covolume_div_covolume_eq_relIndex'
    (ZLattice.comap ℝ L₁ e.toLinearMap) (ZLattice.comap ℝ L₂ e.toLinearMap)
    (fun _ hx => h hx)
  rw [ZLattice.covolume_comap L₁ volume volume (mixedEmbedding.euclidean.volumePreserving_toMixed F),
    ZLattice.covolume_comap L₂ volume volume (mixedEmbedding.euclidean.volumePreserving_toMixed F),
    ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup,
    AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective e.surjective] at hr
  exact hr

private lemma lattice_map (F : Type) [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) :
    (finiteLevelLattice K).toAddSubgroup =
      (finiteLevelFieldSubgroup K).map (mixedEmbedding F).toAddMonoidHom := by
  rfl
private lemma lattice_monotone (F : Type) [Field F] [NumberField F]
    {K H : AddSubgroup (FiniteAdeleRing (𝓞 F) F)} (h : H ≤ K) :
    finiteLevelLattice H ≤ finiteLevelLattice K := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_finiteLevelLattice_iff H x).mp hx
  exact (mem_finiteLevelLattice_iff K _).mpr ⟨y, h hy, rfl⟩
private lemma lattice_relIndex (F : Type) [Field F] [NumberField F]
    (K H : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) :
    (finiteLevelLattice H).toAddSubgroup.relIndex (finiteLevelLattice K).toAddSubgroup =
      (finiteLevelFieldSubgroup H).relIndex (finiteLevelFieldSubgroup K) := by
  rw [lattice_map, lattice_map]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (mixedEmbedding F).injective

private lemma scaled_field (F : Type) [Field F] [NumberField F] (a : ℕ) (ha : 0 < a) :
    finiteLevelFieldSubgroup (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)) =
      integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F) := by
  ext x
  exact FiniteLevelHelpers.scaled_integral_diagonal_iff a ha x

private lemma relIndex_eq_quotient_card (F : Type) [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (a : ℕ) (ha : 0 < a)
    (hK : integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ K) :
    (finiteLevelFieldSubgroup (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F))).relIndex
      (finiteLevelFieldSubgroup K) =
      (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).relIndex K := by
  let U := integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)
  have hFld : finiteLevelFieldSubgroup U = integerScaledSubgroup (a : ℤ) (integerFieldSubgroup F) :=
    scaled_field F a ha
  have h := finiteLevel_quotient_comparison K hcompact hopen a ha hK
  dsimp only at h
  rcases h with ⟨hfin₁, hfin₂, ⟨e, he⟩⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card,
    AddSubgroup.relIndex, AddSubgroup.index_eq_card]
  rw [hFld]
  exact Nat.card_congr e.toEquiv

private lemma comparison_finite (F : Type) [Field F] [NumberField F]
    (μ : Measure (FiniteAdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (a : ℕ) (ha : 0 < a)
    (hK : integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ K) :
    (((integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).relIndex K : ℕ) : ℝ) *
      μ.real (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) : Set _) =
      μ.real (K : Set _) := by
  let U := integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)
  have hfin := (finiteLevel_quotient_comparison K hcompact hopen a ha hK).2.1
  letI : Finite (K ⧸ U.comap K.subtype) := hfin
  have hu : MeasurableSet (U : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (scaled_topology F a ha).2.measurableSet
  have hk : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)) := hopen.measurableSet
  have hm := finiteLevelCovolume_index_mul_measure μ K U hK hk hu
  change ((U.relIndex K : ℕ) : ENNReal) * μ (U : Set _) = μ (K : Set _) at hm
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Measure.real_def, U] using
    congrArg ENNReal.toReal hm

private lemma comparison_arch (F : Type) [Field F] [NumberField F]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (a : ℕ) (ha : 0 < a)
    (hK : integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ K) :
    ZLattice.covolume (finiteLevelLattice (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F))) volume =
      (((integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).relIndex K : ℕ) : ℝ) *
        ZLattice.covolume (finiteLevelLattice K) volume := by
  let U := integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)
  letI : DiscreteTopology (finiteLevelLattice K) := finiteLevelLattice_discrete K hcompact hopen
  letI : IsZLattice ℝ (finiteLevelLattice K) :=
    (finiteLevelLattice_full_rank K hcompact hopen).1
  have hU := scaled_topology F a ha
  letI : DiscreteTopology (finiteLevelLattice U) := finiteLevelLattice_discrete U hU.1 hU.2
  letI : IsZLattice ℝ (finiteLevelLattice U) :=
    (finiteLevelLattice_full_rank U hU.1 hU.2).1
  have hr := mixed_covolume_ratio F (finiteLevelLattice U) (finiteLevelLattice K)
    (lattice_monotone F hK)
  rw [lattice_relIndex F K U, relIndex_eq_quotient_card F K hcompact hopen a ha hK] at hr
  exact (div_eq_iff (ZLattice.covolume_pos (finiteLevelLattice K) volume).ne').mp hr

private lemma cancellation_volume (F : Type) [Field F] [NumberField F]
    (μ : Measure (FiniteAdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ZLattice.covolume (finiteLevelLattice K) volume * μ.real (K : Set _) =
      ZLattice.covolume (finiteLevelLattice (integralFiniteAdeles F)) volume *
        μ.real (integralFiniteAdeles F : Set _) := by
  obtain ⟨a, b, ha, hb, hK, _⟩ := finiteLevel_integer_bounds K hcompact hopen
  have hO : integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) ≤ integralFiniteAdeles F := by
    rintro x ⟨y, hy, rfl⟩
    exact (integralFiniteAdeles F).zsmul_mem hy _
  have hacK := comparison_arch F K hcompact hopen a ha hK
  have hacO := comparison_arch F (integralFiniteAdeles F) (integral_isCompact F) (integral_isOpen F) a ha hO
  have hmK := comparison_finite F μ K hcompact hopen a ha hK
  have hmO := comparison_finite F μ (integralFiniteAdeles F) (integral_isCompact F) (integral_isOpen F) a ha hO
  rw [← hmK, ← hmO]
  calc
    _ = (((integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F)).relIndex K : ℝ) *
        ZLattice.covolume (finiteLevelLattice K) volume) *
        μ.real (integerScaledSubgroup (a : ℤ) (integralFiniteAdeles F) : Set _) := by ring
    _ = _ := by rw [← hacK, hacO]; ring

theorem finiteLevel_covolume_mul_finiteHaar (F : Type) [Field F] [NumberField F]
    (μf : Measure (FiniteAdeleRing (𝓞 F) F)) [μf.IsAddHaarMeasure]
    (hnorm : μf (integralFiniteAdeles F : Set (FiniteAdeleRing (𝓞 F) F)) =
      ENNReal.ofReal (1 / Real.sqrt |(NumberField.discr F : ℝ)|))
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F))) :
    ZLattice.covolume (finiteLevelLattice K)
      (ENNReal.ofReal (PoissonArch.haarScalar F) • volume) *
      μf.real (K : Set (FiniteAdeleRing (𝓞 F) F)) = 1 := by
  letI : DiscreteTopology (finiteLevelLattice K) := finiteLevelLattice_discrete K hcompact hopen
  letI : IsZLattice ℝ (finiteLevelLattice K) :=
    (finiteLevelLattice_full_rank K hcompact hopen).1
  letI : DiscreteTopology (finiteLevelLattice (integralFiniteAdeles F)) :=
    finiteLevelLattice_discrete _ (integral_isCompact F) (integral_isOpen F)
  letI : IsZLattice ℝ (finiteLevelLattice (integralFiniteAdeles F)) :=
    (finiteLevelLattice_full_rank _ (integral_isCompact F) (integral_isOpen F)).1
  have hunit : (0 : ℝ) < Real.sqrt |(NumberField.discr F : ℝ)| := by
    apply Real.sqrt_pos.2
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  calc
    _ = PoissonArch.haarScalar F *
        (ZLattice.covolume (finiteLevelLattice K) volume * μf.real (K : Set _)) := by
      rw [ZLattice.covolume_smul_ofReal _ volume (PoissonArch.haarScalar_pos F)]
      ring
    _ = PoissonArch.haarScalar F *
        (ZLattice.covolume (finiteLevelLattice (integralFiniteAdeles F)) volume *
          μf.real (integralFiniteAdeles F : Set _)) := by
      rw [cancellation_volume F μf K hcompact hopen]
    _ = Real.sqrt |(NumberField.discr F : ℝ)| *
          μf.real (integralFiniteAdeles F : Set _) := by
      rw [← mul_assoc, ← ZLattice.covolume_smul_ofReal _ volume (PoissonArch.haarScalar_pos F),
        integralFiniteLevel_trace_covolume F]
    _ = 1 := by
      rw [Measure.real_def, hnorm, ENNReal.toReal_ofReal (by positivity)]
      field_simp

end
end DedekindZetaZeroFree
