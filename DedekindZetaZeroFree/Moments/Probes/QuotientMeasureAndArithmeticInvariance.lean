module

public import DedekindZetaZeroFree.Moments.Probes.LogWeightFourierSeparation
public import DedekindZetaZeroFree.Adeles.Lattices.SixthPowerUnitDiscreteness
public import DedekindZetaZeroFree.Moments.Probes.GaussianRowDomination
public import DedekindZetaZeroFree.CharacterSums.Gauss.Squarefree.PrincipalNormBound
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.WeightedCoefficients

@[expose] public section

section

namespace DedekindZetaZeroFree
namespace NormalizedProbe
noncomputable section
open scoped NumberField Classical
open NumberField
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace (A.G1 ⧸ A.Gamma1) := borel _

local instance (A : SArithmeticData F) : BorelSpace (A.G1 ⧸ A.Gamma1) := ⟨rfl⟩

theorem exterior_weight_finite (A : SArithmeticData F)
    (W1 : ProbeRealAnnularWeight) (Y : ℝ) (hY : 0 < Y) :
    Set.Finite {s : A.Exterior | W1 (A.exteriorNorm s / Y) ≠ 0} := by
  obtain ⟨M, hM⟩ := W1.compactSupport.bddAbove
  let f : A.Exterior → Ideal (𝓞 F) := fun s => s.val
  have hf : Function.Injective f := fun a b h => Subtype.ext h
  refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈M * Y⌉₊).preimage
    hf.injOn).subset ?_
  intro s hs
  have hb : A.exteriorNorm s / Y ≤ M := hM (subset_tsupport W1 hs)
  have hn : A.exteriorNorm s ≤ M * Y := (div_le_iff₀ hY).mp hb
  have hn' : (Ideal.absNorm s.val : ℝ) ≤ (⌈M * Y⌉₊ : ℝ) :=
    hn.trans (Nat.le_ceil _)
  exact_mod_cast hn'

def scaledIntegralRows (A : SArithmeticData F) (T : ℝ) (K : Set A.G) : Set A.R :=
  {m | ∃ k ∈ K, sLocalDiagonal F A.Sf (m : F) =
    asLocalPoint A (radialSection A T * k)}

private theorem localPoint_mul (A : SArithmeticData F) (x y : A.G) :
    asLocalPoint A (x * y) = asLocalPoint A x * asLocalPoint A y := by
  ext <;> rfl

private theorem localPoint_continuous (A : SArithmeticData F) :
    Continuous (asLocalPoint A) := by
  unfold asLocalPoint SArithmeticData.localToAdditive
  apply Continuous.prodMk
  · exact continuous_pi (fun w => Units.continuous_val.comp
      ((continuous_apply w).comp continuous_fst))
  · exact continuous_pi (fun v => Units.continuous_val.comp
      ((continuous_apply v).comp continuous_snd))

private theorem localPoint_embedding (A : SArithmeticData F) :
    Topology.IsEmbedding (asLocalPoint A) :=
  (Topology.IsEmbedding.piMap (fun _ => Units.isEmbedding_val₀)).prodMap
    (Topology.IsEmbedding.piMap (fun _ => Units.isEmbedding_val₀))

private theorem radial_continuousOn (A : SArithmeticData F) (L : Set ℝ)
    (hL : L ⊆ Set.Ioi 0) : ContinuousOn (radialSection A) L := by
  rw [continuousOn_iff_continuous_restrict]
  have hc := A.continuous_radialSection.comp
    (continuous_subtype_val.subtype_mk (fun r : L => hL r.property))
  convert hc using 1
  funext r
  change radialSection A r.val = A.radialSection r.val (hL r.property)
  exact dif_pos (hL r.property)

theorem common_finite_row_support (A : SArithmeticData F)
    (Ω : Set A.G1) (hΩ : IsCompact (closure Ω))
    (W0 : SLocalProduct F A.Sf → ℂ) (hW0 : HasCompactSupport W0)
    (hUnits : tsupport W0 ⊆ {x | IsUnit x})
    (L : Set ℝ) (hL : IsCompact L) (hLpos : L ⊆ Set.Ioi 0) :
    ∃ K : Set A.G, IsCompact K ∧
      ∀ (W1 : ProbeRealAnnularWeight), tsupport (W1 : ℝ → ℝ) ⊆ L →
      ∀ (X Y : ℝ), 0 < X → 0 < Y →
        Set.Finite (scaledIntegralRows A (X * Y) K) ∧
        ∀ (t : A.G1), t ∈ Ω → ∀ (s : A.Exterior) (m : A.R),
          W1 (A.exteriorNorm s / Y) ≠ 0 →
          W0 (sLocalDiagonal F A.Sf (m : F) *
            asLocalPoint A (((t : A.G) *
              radialSection A (A.exteriorNorm s * X))⁻¹)) ≠ 0 →
          m ∈ scaledIntegralRows A (X * Y) K := by
  let C : Set A.G := (asLocalPoint A) ⁻¹' tsupport W0
  have hCimage : asLocalPoint A '' C = tsupport W0 := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      let u := (hUnits hx).unit
      refine ⟨(ProbeSheet.localUnits A).symm u, ?_, ?_⟩
      · change asLocalPoint A ((ProbeSheet.localUnits A).symm u) ∈ tsupport W0
        have hu : asLocalPoint A ((ProbeSheet.localUnits A).symm u) = x := by
          change (((ProbeSheet.localUnits A) ((ProbeSheet.localUnits A).symm u) :
            (SLocalProduct F A.Sf)ˣ) : SLocalProduct F A.Sf) = x
          rw [MulEquiv.apply_symm_apply]
          exact (hUnits hx).unit_spec
        exact hu ▸ hx
      · change (((ProbeSheet.localUnits A) ((ProbeSheet.localUnits A).symm u) :
          (SLocalProduct F A.Sf)ˣ) : SLocalProduct F A.Sf) = x
        rw [MulEquiv.apply_symm_apply]
        exact (hUnits hx).unit_spec
  have hC : IsCompact C := (localPoint_embedding A).isCompact_iff.mpr
    (hCimage ▸ hW0.isCompact)
  let K : Set A.G := (Set.range fun p : (closure Ω) × L × C =>
    (p.1.val : A.G) * radialSection A p.2.1.val * p.2.2.val)
  have hK : IsCompact K := by
    have hc : Continuous (fun p : (closure Ω) × L × C =>
        (p.1.val : A.G) * radialSection A p.2.1.val * p.2.2.val) := by
      exact ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).mul
        ((continuousOn_iff_continuous_restrict.mp (radial_continuousOn A L hLpos)).comp
          (continuous_fst.comp continuous_snd))).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
    letI : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hΩ
    letI : CompactSpace L := isCompact_iff_compactSpace.mp hL
    letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
    exact isCompact_range hc
  refine ⟨K, hK, ?_⟩
  intro W1 hW1 X Y hX hY
  have hfinite : Set.Finite (scaledIntegralRows A (X * Y) K) := by
    have hf := probe_additive_box_rows_finite F A.Sf (X * Y)
      (asLocalPoint A '' K) (hK.image (localPoint_continuous A))
    apply hf.subset
    rintro m ⟨k, hk, he⟩
    change sLocalDiagonal F A.Sf (m : F) ∈
      (fun x => ProbeAdditive.balancedDilation F A.Sf (X * Y) * x) ''
        (asLocalPoint A '' K)
    refine ⟨asLocalPoint A k, ⟨k, hk, rfl⟩, ?_⟩
    rw [he, localPoint_mul]
    simp only [radialSection, dif_pos (mul_pos hX hY), asLocalPoint,
      SArithmeticData.localToAdditive_radialSection]
  refine ⟨hfinite, ?_⟩
  intro t ht s m hs hm
  let r := A.exteriorNorm s / Y
  have hr : r ∈ L := hW1 (subset_tsupport W1 hs)
  have hrpos : 0 < r := hLpos hr
  let x := sLocalDiagonal F A.Sf (m : F) *
    asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹)
  have hx : x ∈ tsupport W0 := subset_tsupport W0 hm
  let u := (hUnits hx).unit
  let c := (ProbeSheet.localUnits A).symm u
  have hc : asLocalPoint A c = x := by
    change (((ProbeSheet.localUnits A) ((ProbeSheet.localUnits A).symm u) :
      (SLocalProduct F A.Sf)ˣ) : SLocalProduct F A.Sf) = x
    rw [MulEquiv.apply_symm_apply]
    exact (hUnits hx).unit_spec
  have hcC : c ∈ C := by
    change asLocalPoint A c ∈ tsupport W0
    rw [hc]
    exact hx
  refine ⟨(t : A.G) * radialSection A r * c, ?_, ?_⟩
  · exact ⟨(⟨t, subset_closure ht⟩, ⟨r, hr⟩, ⟨c, hcC⟩), rfl⟩
  · have hscale : radialSection A (X * Y) * radialSection A r =
        radialSection A (A.exteriorNorm s * X) := by
      simp only [radialSection, dif_pos (mul_pos hX hY), dif_pos hrpos,
        dif_pos (mul_pos (A.exteriorNorm_pos s) hX)]
      rw [← A.radialSection_mul]
      congr 1
      dsimp [r]
      field_simp
    have he : radialSection A (X * Y) * ((t : A.G) * radialSection A r * c) =
        ((t : A.G) * radialSection A (A.exteriorNorm s * X)) * c := by
      calc
        _ = (t : A.G) * (radialSection A (X * Y) * radialSection A r) * c := by ac_rfl
        _ = _ := by rw [hscale]
    rw [he, localPoint_mul, hc]
    dsimp [x]
    have hinv : asLocalPoint A ((t : A.G) * radialSection A (A.exteriorNorm s * X)) *
        asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹) = 1 := by
      rw [← localPoint_mul, mul_inv_cancel]
      rfl
    calc
      _ = sLocalDiagonal F A.Sf (m : F) * 1 := (mul_one _).symm
      _ = _ := by rw [← hinv]; ac_rfl

theorem original_zero_row (A : SArithmeticData F)
    (W0 : SLocalProduct F A.Sf → ℂ) (hUnits : tsupport W0 ⊆ {x | IsUnit x})
    (t : A.G1) (T : ℝ) :
    W0 (sLocalDiagonal F A.Sf (0 : F) *
      asLocalPoint A (((t : A.G) * radialSection A T)⁻¹)) = 0 := by
  have hz : W0 (0 : SLocalProduct F A.Sf) = 0 := by
    by_contra h
    have hu := hUnits (subset_tsupport W0 (show (0 : SLocalProduct F A.Sf) ∈
      Function.support W0 from h))
    exact not_isUnit_zero hu
  have hd : sLocalDiagonal F A.Sf (0 : F) = 0 := by
    ext <;> simp [sLocalDiagonal]
  rw [hd, zero_mul, hz]

set_option maxHeartbeats 800000

private theorem annular_weight_continuous (A : SArithmeticData F)
    (W : SLocalProduct F A.Sf → ℂ)
    (hW : ProbeWeight.IsAnnularTensor F A.Sf W) : Continuous W := by
  obtain ⟨fr, fc, ff, hr, hc, hf, heq⟩ := hW
  have hm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)
    · apply continuous_pi
      intro v
      exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1)
  rw [show W = _ from funext heq]
  apply Continuous.mul
  · apply Continuous.mul
    · apply continuous_finset_prod
      intro v hv
      exact (hr v).1.continuous.comp ((continuous_apply v).comp
        (continuous_fst.comp (hm.comp continuous_fst)))
    · apply continuous_finset_prod
      intro v hv
      exact (hc v).1.continuous.comp ((continuous_apply v).comp
        (continuous_snd.comp (hm.comp continuous_fst)))
  · apply continuous_finset_prod
    intro v hv
    exact (hf v).1.continuous.comp ((continuous_apply v).comp continuous_snd)

private theorem residue_character_norm_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · simp [χ.map_nonunit hr]

theorem principal_rowB_absolutely_convergent (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (m : ThetaReflectionData.Row A)
    (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      ‖ThetaReflectionData.forwardSummand A P.coefficients m Z i.1 i.2‖) := by
  obtain ⟨C, hC, hdom⟩ := ProbePoissonGaussianRowBound.gaussian_row_domination
    A σ η hS 2 Z (by norm_num) hZ
  have hs := (hdom P).2.2.2.1
  refine hs.of_nonneg_of_le (fun i => norm_nonneg _) ?_
  intro i
  let D := P.coefficients
  letI := D.finiteResidue (ThetaReflectionData.forwardModulus A D i.1 i.2)
    (mul_ne_zero (D.generates i.1.val).1 (pow_ne_zero _ (D.generates i.2).1))
  have hc : ‖ThetaReflectionData.forwardRowCharacter A D i.1 i.2 m.val‖ ≤ 1 :=
    residue_character_norm_le_one _ _
  have hq : 1 ≤ A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 :=
    one_le_mul_of_one_le_of_one_le (idealNorm_ge_one _ i.1.val.property.1)
      (one_le_pow₀ (idealNorm_ge_one _ i.2.property.1))
  have hp : 1 ≤ (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3) ^ (2 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hd : 0 ≤ Real.sqrt (A.exteriorNorm i.1.val) * A.exteriorNorm i.2 := by
    have := A.exteriorNorm_pos i.2
    positivity
  have hn := norm_nonneg (ThetaReflectionData.forwardArithmeticWeight A D i.1 i.2)
  have hg := abs_nonneg (thetaReflectionGaussian
    (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z))
  change _ ≤ ProbePoissonGaussianRowBound.rowMass A D 2 Z i.1 i.2
  rw [ThetaReflectionData.forwardSummand, norm_div, norm_mul, norm_mul,
    norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (A.exteriorNorm_pos i.2)]
  unfold ProbePoissonGaussianRowBound.rowMass
  calc
    _ ≤ ‖ThetaReflectionData.forwardArithmeticWeight A D i.1 i.2‖ *
        |thetaReflectionGaussian (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z)| /
        (Real.sqrt (A.exteriorNorm i.1.val) * A.exteriorNorm i.2) := by
      apply div_le_div_of_nonneg_right _ hd
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc hn) hg
    _ = (‖ThetaReflectionData.forwardArithmeticWeight A D i.1 i.2‖ /
        (Real.sqrt (A.exteriorNorm i.1.val) * A.exteriorNorm i.2)) *
        |thetaReflectionGaussian (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z)| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (div_nonneg hn hd) hp) hg

def expandedProbeSummand (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (X Y Z : ℝ) (t : A.G1) (s : A.Exterior) (m : A.R)
    (i : ExteriorSquarefreeIdeal A.cS × A.Exterior) : ℂ :=
  if hm : m = 0 then 0 else
    (Y⁻¹ : ℂ) * (W1 (A.exteriorNorm s / Y) : ℂ) *
      (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * gaussRow A D s m *
      W0 (sLocalDiagonal F A.Sf (m : F) *
        asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹)) *
      ThetaReflectionData.forwardSummand A D ⟨m, hm⟩ Z i.1 i.2

theorem principal_inserted_absolutely_convergent (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (t : A.G1) :
    Summable (fun j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
      ‖expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
        j.1 j.2.1 j.2.2‖) := by
  obtain ⟨K, hK, hrows⟩ := common_finite_row_support A {t}
    (by simpa using isCompact_singleton) P.W0 P.compactSupport P.supportUnits
    (tsupport (P.W1 : ℝ → ℝ)) P.W1.compactSupport P.W1.support_positive
  obtain ⟨hfinite, hsupport⟩ := hrows P.W1 (Set.Subset.refl _) X Y hX hY
  let f := fun j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
    ‖expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t j.1 j.2.1 j.2.2‖
  have hinner : ∀ s m, Summable (fun i => f (s, m, i)) := by
    intro s m
    by_cases hm : m = 0
    · simp [f, expandedProbeSummand, hm]
    · simpa only [f, expandedProbeSummand, dif_neg hm, norm_mul] using
        (principal_rowB_absolutely_convergent A σ η hS P ⟨m, hm⟩ Z hZ).mul_left
          ‖(Y⁻¹ : ℂ) * (P.W1 (A.exteriorNorm s / Y) : ℂ) *
            (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ *
            gaussRow A P.coefficients s m * P.W0
              (sLocalDiagonal F A.Sf (m : F) *
                asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹))‖
  have hzero : ∀ s m, P.W1 (A.exteriorNorm s / Y) = 0 ∨
      m ∉ scaledIntegralRows A (X * Y) K → ∀ i, f (s, m, i) = 0 := by
    intro s m h i
    have hw : P.W1 (A.exteriorNorm s / Y) = 0 ∨
        P.W0 (sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹)) = 0 := by
      rcases h with h | h
      · exact Or.inl h
      · by_cases hs : P.W1 (A.exteriorNorm s / Y) = 0
        · exact Or.inl hs
        · exact Or.inr (by by_contra hn; exact h (hsupport t (by simp) s m hs hn))
    rcases hw with hw | hw <;>
      simp only [f, expandedProbeSummand, hw, Complex.ofReal_zero, mul_zero,
        zero_mul, dite_eq_ite, ite_self, norm_zero]
  apply (summable_prod_of_nonneg (fun j => norm_nonneg _)).mpr
  refine ⟨?_, ?_⟩
  · intro s
    apply (summable_prod_of_nonneg (fun j => norm_nonneg _)).mpr
    refine ⟨hinner s, ?_⟩
    apply summable_of_finite_support
    apply hfinite.subset
    intro m hm
    by_contra hn
    apply hm
    change (∑' i, f (s, m, i)) = 0
    simp only [hzero s m (Or.inr hn), tsum_zero]
  · apply summable_of_finite_support
    apply (exterior_weight_finite A P.W1 Y hY).subset
    intro s hs
    by_contra hn
    apply hs
    change (∑' j : A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior), f (s, j)) = 0
    have hz : ∀ j : A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior), f (s, j) = 0 :=
      fun j => hzero s j.1 (Or.inl (not_ne_iff.mp hn)) j.2
    simp only [hz, tsum_zero]

set_option maxHeartbeats 800000 in

theorem principal_integrated_absolutely_convergent (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (∑' j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior),
      ∫⁻ t in P.domain.domain,
        ENNReal.ofReal ‖expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
          j.1 j.2.1 j.2.2‖ ∂P.domain.measure) < ⊤ := by
  letI := P.domain.haar
  have hmass : P.domain.measure P.domain.domain < ⊤ :=
    (measure_mono subset_closure).trans_lt P.domain.relativelyCompact.measure_lt_top
  obtain ⟨K, _, hK⟩ := common_finite_row_support A P.domain.domain
    P.domain.relativelyCompact P.W0 P.compactSupport P.supportUnits
    (tsupport (P.W1 : ℝ → ℝ)) P.W1.compactSupport P.W1.support_positive
  obtain ⟨hM, hsupp⟩ := hK P.W1 (Set.Subset.refl _) X Y hX hY
  let M := hM.toFinset
  let S := (exterior_weight_finite A P.W1 Y hY).toFinset
  let f := fun (s : A.Exterior) (m : A.R)
      (i : ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
    ∫⁻ t in P.domain.domain,
      ENNReal.ofReal ‖expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t s m i‖
      ∂P.domain.measure
  have hz : ∀ s m, s ∉ S ∨ m ∉ M → ∀ i, f s m i = 0 := by
    intro s m h i
    apply setLIntegral_eq_zero P.domain.measurable
    intro t ht
    have hw : P.W1 (A.exteriorNorm s / Y) = 0 ∨
        P.W0 (sLocalDiagonal F A.Sf (m : F) *
          asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹)) = 0 := by
      rcases h with h | h
      · exact Or.inl (not_ne_iff.mp (fun hn => h
          ((exterior_weight_finite A P.W1 Y hY).mem_toFinset.mpr hn)))
      · by_cases hs : P.W1 (A.exteriorNorm s / Y) = 0
        · exact Or.inl hs
        · apply Or.inr
          by_contra hn
          exact h (hM.mem_toFinset.mpr (hsupp t ht s m hs hn))
    rcases hw with hw | hw <;>
      simp only [expandedProbeSummand, hw, Complex.ofReal_zero, mul_zero, zero_mul,
        dite_eq_ite, ite_self, norm_zero, ENNReal.ofReal_zero, Pi.zero_apply]
  obtain ⟨B, hB⟩ := (annular_weight_continuous A P.W0 P.annular).norm.bddAbove_range_of_hasCompactSupport P.compactSupport.norm
  have hbound : ∀ x, ‖P.W0 x‖ ≤ B := fun x => hB ⟨x, rfl⟩
  have hBpos : 0 ≤ B := (norm_nonneg (P.W0 0)).trans (hbound 0)
  have hi : ∀ s m, (∑' i, f s m i) < ⊤ := by
    intro s m
    by_cases hm : m = 0
    · subst m
      simp [f, expandedProbeSummand]
    · let C : ℝ := ‖(Y⁻¹ : ℂ) * (P.W1 (A.exteriorNorm s / Y) : ℂ) *
          (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * gaussRow A P.coefficients s m‖ * B
      have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) hBpos
      have hd : ∀ i, f s m i ≤ ENNReal.ofReal
          (C * ‖ThetaReflectionData.forwardSummand A P.coefficients ⟨m, hm⟩ Z i.1 i.2‖) *
            P.domain.measure P.domain.domain := by
        intro i
        calc
          f s m i ≤ ∫⁻ t in P.domain.domain, ENNReal.ofReal
              (C * ‖ThetaReflectionData.forwardSummand A P.coefficients ⟨m, hm⟩ Z i.1 i.2‖)
              ∂P.domain.measure := by
            apply lintegral_mono
            intro t
            apply ENNReal.ofReal_le_ofReal
            simp only [expandedProbeSummand, dif_neg hm, norm_mul]
            simp only [C, norm_mul]
            gcongr
            exact hbound _
          _ = _ := by simp
      calc
        (∑' i, f s m i) ≤ ∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior, ENNReal.ofReal
            (C * ‖ThetaReflectionData.forwardSummand A P.coefficients ⟨m, hm⟩ Z i.1 i.2‖) *
              P.domain.measure P.domain.domain := by
                exact ENNReal.tsum_le_tsum (f := fun i => f s m i) hd
        _ = (∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior, ENNReal.ofReal
            (C * ‖ThetaReflectionData.forwardSummand A P.coefficients ⟨m, hm⟩ Z i.1 i.2‖)) *
              P.domain.measure P.domain.domain := ENNReal.tsum_mul_right
        _ < ⊤ := ENNReal.mul_lt_top
          (((principal_rowB_absolutely_convergent A σ η hS P ⟨m, hm⟩ Z hZ).mul_left C).tsum_ofReal_lt_top) hmass
  change (∑' j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior),
    f j.1 j.2.1 j.2.2) < ⊤
  rw [ENNReal.tsum_prod (f := fun (s : A.Exterior) (j : A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) => f s j.1 j.2)]
  rw [tsum_eq_sum (s := S)]
  · apply ENNReal.sum_lt_top.mpr
    intro s hs
    rw [ENNReal.tsum_prod (f := fun m i => f s m i)]
    rw [tsum_eq_sum (s := M)]
    · exact ENNReal.sum_lt_top.mpr (fun m hm => hi s m)
    · intro m hm
      simp only [hz s m (Or.inr hm), tsum_zero]
  · intro s hs
    have he : ∀ j : A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior),
        f s j.1 j.2 = 0 := fun j => hz s j.1 (Or.inl hs) j.2
    simp only [he, tsum_zero]

theorem principal_expansion_valid (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : PrincipalData A σ η hS) (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (∀ j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior),
      IntegrableOn (fun t => expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
        j.1 j.2.1 j.2.2) P.domain.domain P.domain.measure) ∧
    (∀ t, integrand A P.coefficients P.domain P.W0 P.W1 X Y Z t =
      ∑' j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior),
        expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
          j.1 j.2.1 j.2.2) ∧
    probe A P.coefficients P.domain P.W0 P.W1 X Y Z =
      ∑' j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior),
        ∫ t in P.domain.domain,
          expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
            j.1 j.2.1 j.2.2 ∂P.domain.measure := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hcount := (ProbeExteriorIdealCount.ideal_norm_summable F A.cS 2
    (by norm_num)).countable_support
  have hall : Function.support (fun I : A.Exterior =>
      (idealNorm I.val) ^ (-(2 : ℝ))) = Set.univ := by
    ext I
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (A.exteriorNorm_pos I) _).ne'
  rw [hall] at hcount
  letI : Countable A.Exterior := Set.countable_univ_iff.mp hcount
  letI : Countable (ExteriorSquarefreeIdeal A.cS) :=
    inferInstanceAs (Countable {I : A.Exterior // Squarefree I.val})
  letI := P.domain.haar
  let f := fun (j : A.Exterior × A.R × (ExteriorSquarefreeIdeal A.cS × A.Exterior))
    (t : A.G1) => expandedProbeSummand A P.coefficients P.W0 P.W1 X Y Z t
      j.1 j.2.1 j.2.2
  have hw : ∀ s m, Continuous (fun t : A.G1 => P.W0
      (sLocalDiagonal F A.Sf (m : F) *
        asLocalPoint A (((t : A.G) * radialSection A (A.exteriorNorm s * X))⁻¹))) := by
    intro s m
    have hc : Continuous (asLocalPoint A) := by
      unfold asLocalPoint SArithmeticData.localToAdditive
      apply Continuous.prodMk
      · exact continuous_pi (fun w => Units.continuous_val.comp
          ((continuous_apply w).comp continuous_fst))
      · exact continuous_pi (fun v => Units.continuous_val.comp
          ((continuous_apply v).comp continuous_snd))
    exact (ProbeLogWeight.continuous_weight A P.W0 P.annular).comp
      (continuous_const.mul (hc.comp ((continuous_subtype_val.mul continuous_const).inv)))
  have hc : ∀ j, Continuous (f j) := by
    intro j
    dsimp [f]
    unfold expandedProbeSummand
    split
    · exact continuous_const
    · exact (continuous_const.mul (hw j.1 j.2.1)).mul continuous_const
  have hi : ∀ j, IntegrableOn (f j) P.domain.domain P.domain.measure := fun j =>
    ((hc j).continuousOn.integrableOn_compact P.domain.relativelyCompact).mono_set
      subset_closure
  have heq : ∀ t, integrand A P.coefficients P.domain P.W0 P.W1 X Y Z t =
      ∑' j, f j t := by
    intro t
    have hs : Summable (fun j => f j t) :=
      (principal_inserted_absolutely_convergent A σ η hS P X Y Z hX hY hZ t).of_norm
    rw [hs.tsum_prod]
    unfold integrand
    rw [← tsum_mul_left]
    apply tsum_congr
    intro s
    rw [(hs.prod_factor s).tsum_prod]
    simp only [← tsum_mul_left]
    apply tsum_congr
    intro m
    by_cases hm : m = 0
    · subst m
      simp [f, expandedProbeSummand, rowB]
    · simp only [f, expandedProbeSummand, dif_neg hm, rowB,
        ThetaReflectionData.forwardB]
      simp only [← tsum_mul_left]
      congr 1
      ring
  refine ⟨hi, heq, ?_⟩
  unfold probe
  simp only [heq]
  apply integral_tsum (fun j => (hi j).aestronglyMeasurable)
  simpa only [f, ofReal_norm_eq_enorm] using
    (principal_integrated_absolutely_convergent A σ η hS P X Y Z hX hY hZ).ne

end
end NormalizedProbe
end DedekindZetaZeroFree

end
