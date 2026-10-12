module

public import DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators
public import DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveRowBoxesAndSchurBounds

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain

namespace SArithmeticData

def localToAdditive {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (x : A.G) : SLocalProduct F A.Sf :=
  (fun w => (x.1 w : w.Completion), fun v => (x.2 v : v.val.adicCompletion F))

theorem localToAdditive_radialSection {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) :
    A.localToAdditive (A.radialSection T hT) =
      ProbeAdditive.balancedDilation F A.Sf T := by
  have hd : Module.finrank ℚ F = 2 * InfinitePlace.nrComplexPlaces F := by
    have hreal := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide : 2 < 12) A.primitive_zeta12
    simpa [hreal] using (InfinitePlace.card_add_two_mul_card_eq_rank (K := F)).symm
  apply Prod.ext
  · change (fun w => ((A.radialSection T hT).1 w : w.Completion)) = _
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
          (T ^ (1 / (Module.finrank ℚ F : ℝ)) • (1 : mixedEmbedding.mixedSpace F)))
    rw [RingEquiv.apply_symm_apply]
    apply Prod.ext
    · funext v
      exact False.elim ((InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place v.val)) v.property)
    · funext v
      change InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property
        ((A.radialSection T hT).1 v.val : v.val.Completion) = _
      simp [radialSection, hd]
  · rfl

structure BalancedIdealSection {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G) where
  generator : A.Exterior → A.R
  fieldUnit : A.Exterior → Fˣ
  generates : ∀ I : A.Exterior, A.Generates I (generator I)
  fieldUnit_coe : ∀ I : A.Exterior, (fieldUnit I : F) = (generator I : F)
  allowed : ∀ I : A.Exterior, A.IsAllowed B (fieldUnit I)
  balanced : ∀ I : A.Exterior,
    A.diagonal (fieldUnit I) /
      A.radialSection (A.exteriorNorm I) (A.exteriorNorm_pos I) ∈ K_bal

theorem balanced_ideal_section_injective {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (s : A.BalancedIdealSection B K_bal) : Function.Injective s.generator := by
  intro I J h
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  rw [A.exteriorIdealEquiv_apply, A.exteriorIdealEquiv_apply,
    ← (s.generates I).2, ← (s.generates J).2, h]

def balancedDyadicBox {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (K_bal : Set A.G) : Set (SLocalProduct F A.Sf) :=
  (fun p : ℝ × A.G =>
    ProbeAdditive.balancedDilation F A.Sf p.1 * A.localToAdditive p.2) ''
      (Set.Icc (1 / 2 : ℝ) 1 ×ˢ K_bal)

def balancedDyadicIdeals {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (X : ℝ) : Set A.Exterior :=
  {I | X / 2 < A.exteriorNorm I ∧ A.exteriorNorm I ≤ X}

private theorem continuous_localToAdditive {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) : Continuous A.localToAdditive := by
  unfold localToAdditive
  apply Continuous.prodMk
  · apply continuous_pi
    intro w
    exact Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)
  · apply continuous_pi
    intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)

private theorem localToAdditive_mul {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (x y : A.G) :
    A.localToAdditive (x * y) = A.localToAdditive x * A.localToAdditive y := by
  ext w <;> rfl

private theorem localToAdditive_diagonal {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (a : Fˣ) :
    A.localToAdditive (A.diagonal a) = sLocalDiagonal F A.Sf (a : F) := by
  ext w <;> rfl

private theorem balancedDyadicBox_compact {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (K_bal : Set A.G) (hK : IsCompact K_bal) :
    IsCompact (A.balancedDyadicBox K_bal) := by
  apply (isCompact_Icc.prod hK).image_of_continuousOn
  have hrad : ContinuousOn (fun t : ℝ => ProbeAdditive.balancedDilation F A.Sf t)
      (Set.Icc (1 / 2 : ℝ) 1) := by
    have hc := A.continuous_localToAdditive.comp A.continuous_radialSection
    have hp : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, 0 < t := by
      intro t ht
      linarith [ht.1]
    apply continuousOn_iff_continuous_restrict.mpr
    change Continuous (fun t : Set.Icc (1 / 2 : ℝ) 1 =>
      ProbeAdditive.balancedDilation F A.Sf t.val)
    have hsub : Continuous (fun t : Set.Icc (1 / 2 : ℝ) 1 =>
        (⟨t.val, hp t.val t.property⟩ : {t : ℝ // 0 < t})) :=
      continuous_subtype_val.subtype_mk _
    simpa only [Function.comp_def, Set.domRestrict, A.localToAdditive_radialSection] using hc.comp hsub
  exact (hrad.comp continuousOn_fst (fun p hp => hp.1)).mul
    (A.continuous_localToAdditive.continuousOn.comp continuousOn_snd (fun p hp => hp.2))

private theorem balanced_generator_row {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (s : A.BalancedIdealSection B K_bal) (X : ℝ) (hX : 0 < X)
    (I : A.Exterior) (hI : I ∈ A.balancedDyadicIdeals X) :
    s.generator I ∈ ProbeAdditive.boxRows F A.Sf X (A.balancedDyadicBox K_bal) := by
  let N := A.exteriorNorm I
  let hN := A.exteriorNorm_pos I
  let t := N / X
  have ht : 0 < t := div_pos hN hX
  let k := A.diagonal (s.fieldUnit I) / A.radialSection N hN
  have hk : k ∈ K_bal := s.balanced I
  have htI : t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hX).mpr
      have := hI.1
      dsimp [N]
      linarith
    · exact (div_le_one hX).mpr hI.2
  change sLocalDiagonal F A.Sf (s.generator I : F) ∈
    (fun x => ProbeAdditive.balancedDilation F A.Sf X * x) '' A.balancedDyadicBox K_bal
  refine ⟨ProbeAdditive.balancedDilation F A.Sf t * A.localToAdditive k,
    ⟨(t, k), ⟨htI, hk⟩, rfl⟩, ?_⟩
  dsimp only
  rw [← A.localToAdditive_radialSection X hX,
    ← A.localToAdditive_radialSection t ht, ← A.localToAdditive_mul,
    ← A.localToAdditive_mul, ← mul_assoc, ← A.radialSection_mul]
  have hprod : X * t = N := by dsimp [t]; field_simp
  have hmul : A.radialSection (X * t) (mul_pos hX ht) * k =
      A.diagonal (s.fieldUnit I) := by
    simp only [hprod]
    dsimp [k]
    exact mul_div_cancel _ _
  rw [hmul, A.localToAdditive_diagonal, s.fieldUnit_coe]

theorem detector_balanced_ideal_section {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (hK : IsCompact K_bal) (s : A.BalancedIdealSection B K_bal) :
    IsCompact (A.balancedDyadicBox K_bal) ∧
    Function.Injective s.generator ∧
    (∀ X : ℝ, 1 ≤ X →
      (A.balancedDyadicIdeals X).Finite ∧
      Set.MapsTo s.generator (A.balancedDyadicIdeals X)
        (ProbeAdditive.boxRows F A.Sf X (A.balancedDyadicBox K_bal))) ∧
    (∀ I : A.Exterior, A.exteriorNorm I = 1 →
      s.generator I ∈ ProbeAdditive.boxRows F A.Sf 1 (A.balancedDyadicBox K_bal)) := by
  have hc := A.balancedDyadicBox_compact K_bal hK
  have hi := A.balanced_ideal_section_injective B K_bal s
  refine ⟨hc, hi, ?_, ?_⟩
  · intro X hX
    have hm : Set.MapsTo s.generator (A.balancedDyadicIdeals X)
        (ProbeAdditive.boxRows F A.Sf X (A.balancedDyadicBox K_bal)) := by
      intro I hI
      exact A.balanced_generator_row B K_bal s X (by linarith) I hI
    refine ⟨?_, hm⟩
    exact (probe_additive_box_rows_finite F A.Sf X (A.balancedDyadicBox K_bal) hc).of_injOn
      hm hi.injOn
  · intro I hI
    apply A.balanced_generator_row B K_bal s 1 (by norm_num) I
    change 1 / 2 < A.exteriorNorm I ∧ A.exteriorNorm I ≤ 1
    rw [hI]
    norm_num

def balancedTransportCoeff {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (s : A.BalancedIdealSection B K_bal) (T : Finset A.Exterior)
    (a : A.Exterior → ℂ) (m : A.R) : ℂ :=
  if h : ∃ I : A.Exterior, I ∈ T ∧ s.generator I = m then a (Classical.choose h) else 0

theorem balancedTransportCoeff_generator {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (s : A.BalancedIdealSection B K_bal) (T : Finset A.Exterior)
    (a : A.Exterior → ℂ) (I : A.Exterior) (hI : I ∈ T) :
    A.balancedTransportCoeff B K_bal s T a (s.generator I) = a I := by
  have h : ∃ J : A.Exterior, J ∈ T ∧ s.generator J = s.generator I := ⟨I, hI, rfl⟩
  rw [balancedTransportCoeff, dif_pos h]
  congr 1
  exact A.balanced_ideal_section_injective B K_bal s (Classical.choose_spec h).2

theorem balancedTransportCoeff_zero {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (s : A.BalancedIdealSection B K_bal) (T : Finset A.Exterior)
    (a : A.Exterior → ℂ) (m : A.R) (hm : m ∉ T.image s.generator) :
    A.balancedTransportCoeff B K_bal s T a m = 0 := by
  apply dif_neg
  rintro ⟨I, hI, h⟩
  exact hm (Finset.mem_image.mpr ⟨I, hI, h⟩)

theorem balanced_ideal_section_energy {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V) (K_bal : Set A.G)
    (hK : IsCompact K_bal) (s : A.BalancedIdealSection B K_bal)
    (X : ℝ) (hX : 1 ≤ X) (T : Finset A.Exterior)
    (hT : ∀ I ∈ T, I ∈ A.balancedDyadicIdeals X) (a : A.Exterior → ℂ) :
    let rows := (probe_additive_box_rows_finite F A.Sf X
      (A.balancedDyadicBox K_bal) (detector_balanced_ideal_section A B K_bal hK s).1).toFinset
    T.image s.generator ⊆ rows ∧
      (∑ m ∈ rows, ‖A.balancedTransportCoeff B K_bal s T a m‖ ^ 2) =
        ∑ I ∈ T, ‖a I‖ ^ 2 := by
  dsimp only
  let rows := (probe_additive_box_rows_finite F A.Sf X
    (A.balancedDyadicBox K_bal) (detector_balanced_ideal_section A B K_bal hK s).1).toFinset
  have hsub : T.image s.generator ⊆ rows := by
    intro m hm
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hm
    apply Set.Finite.mem_toFinset _ |>.mpr
    exact (detector_balanced_ideal_section A B K_bal hK s).2.2.1 X hX |>.2 (hT I hI)
  refine ⟨hsub, ?_⟩
  calc
    _ = ∑ m ∈ T.image s.generator, ‖A.balancedTransportCoeff B K_bal s T a m‖ ^ 2 := by
      symm
      apply Finset.sum_subset hsub
      intro m hm hnot
      rw [A.balancedTransportCoeff_zero B K_bal s T a m hnot]
      simp
    _ = ∑ I ∈ T, ‖A.balancedTransportCoeff B K_bal s T a (s.generator I)‖ ^ 2 := by
      apply Finset.sum_image
      intro I hI J hJ h
      exact A.balanced_ideal_section_injective B K_bal s h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [A.balancedTransportCoeff_generator B K_bal s T a I hI]

end SArithmeticData
end
end DedekindZetaZeroFree
