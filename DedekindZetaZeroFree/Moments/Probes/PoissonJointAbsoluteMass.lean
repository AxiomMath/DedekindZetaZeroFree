module

public import DedekindZetaZeroFree.CharacterSums.Gauss.SixthPowerUnitInvariance
public import DedekindZetaZeroFree.MeasureTheory.IntegratedNormMassTransfer
public import DedekindZetaZeroFree.Moments.Probes.RadialFourierSheetTranslation
public import DedekindZetaZeroFree.Moments.Probes.GaussianDoubleMomentSummability
public import DedekindZetaZeroFree.Moments.Probes.QuotientMeasureAndArithmeticInvariance
public import DedekindZetaZeroFree.Moments.Probes.NormOneFrequencyShape

@[expose] public section

namespace DedekindZetaZeroFree
namespace ProbeJointAbsoluteMass
noncomputable section
open scoped NumberField Classical ENNReal
open MeasureTheory NumberField

variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _
local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

def modulusNorm (A : SArithmeticData F)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) : ℝ :=
  A.exteriorNorm c.val * A.exteriorNorm n ^ 3

def lambda (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) (Z : ℝ) : ℂ :=
  ThetaReflectionData.forwardArithmeticWeight A D c n *
    (thetaReflectionGaussian (modulusNorm A c n / Z) : ℂ) /
    ((Real.sqrt (A.exteriorNorm c.val) : ℂ) * (A.exteriorNorm n : ℂ))

abbrev Index (A : SArithmeticData F) :=
  A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior × ThetaReflectionData.Row A

def frequency (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (X : ℝ) (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS)
    (n : A.Exterior) (h : ThetaReflectionData.Row A) : SLocalProduct F A.Sf :=
  (ProbeSheet.ell A (A.exteriorNorm s * X)).val *
    sLocalDiagonal F A.Sf ((h.val : F) /
      ((D.generator s : F) * (ThetaReflectionData.forwardModulus A D c n : F)))

def kernel (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (X Y Z : ℝ) (i : Index A) (t : A.G1) : ℂ :=
  (Y⁻¹ : ℂ) * (P.W1 (A.exteriorNorm i.1 / Y) : ℂ) *
    lambda A P.coefficients i.2.1 i.2.2.1 Z *
    ((Real.sqrt X / modulusNorm A i.2.1 i.2.2.1 : ℝ) : ℂ) *
    comparisonPoissonFiniteCoefficient F A P.coefficients
      i.2.1 i.2.2.1 i.1 i.2.2.2.val *
    ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
      ((ProbeSheet.localUnits A t.val).val *
        frequency A P.coefficients X i.1 i.2.1 i.2.2.1 i.2.2.2)

def absoluteMass (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS) (X Y Z : ℝ) : ℝ≥0∞ :=
  ∑' i : Index A, ∫⁻ t in P.domain.domain,
    ENNReal.ofReal ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure

def outerMoment (A : SArithmeticData F) (W1 : ProbeRealAnnularWeight) (Y : ℝ) : ℝ :=
  ∑' s : A.Exterior, |W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s

def gaussianMomentTerm (A : SArithmeticData F) (σ Z : ℝ)
    (p : ExteriorSquarefreeIdeal A.cS × A.Exterior) : ℝ :=
  (A.exteriorNorm p.1.val) ^ (σ - 1 / 2) *
    (A.exteriorNorm p.2) ^ (3 * σ - 1) *
    thetaReflectionGaussian (modulusNorm A p.1 p.2 / Z)

def gaussianMoment (A : SArithmeticData F) (σ Z : ℝ) : ℝ :=
  ∑' p : ExteriorSquarefreeIdeal A.cS × A.Exterior, gaussianMomentTerm A σ Z p

abbrev OrbitIndex (A : SArithmeticData F) :=
  A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior × ProbeOrbitNormSum.Orbit A

def orbitIntegral (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS) (X Y Z : ℝ)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (i : OrbitIndex A) : ℂ :=
  ∫ t : A.G1, kernel A ι η hS P X Y Z (i.1, i.2.1, i.2.2.1, ρ i.2.2.2) t
    ∂P.domain.measure

theorem joint_series_exchanges {T I : Type*} [MeasurableSpace T] [Countable I]
    (μ : Measure T) (f : I → T → ℂ)
    (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable (fun i => ∫ t, ‖f i t‖ ∂μ)) :
    (∀ᵐ t ∂μ, Summable (fun i => ‖f i t‖) ∧ Summable (fun i => f i t)) ∧
    Integrable (fun t => ∑' i, f i t) μ ∧
    Summable (fun i => ‖∫ t, f i t ∂μ‖) ∧
    (∫ t, ∑' i, f i t ∂μ) = ∑' i, ∫ t, f i t ∂μ ∧
    (∀ (J : Type) (e : J ≃ I), (∫ t, ∑' j, f (e j) t ∂μ) =
      ∑' i, ∫ t, f i t ∂μ) ∧
    (∀ (J : Type) (g : I → J),
      Summable (fun j => ‖∑' i : {i // g i = j}, ∫ t, f i.val t ∂μ‖) ∧
      (∑' j, ∑' i : {i // g i = j}, ∫ t, f i.val t ∂μ) =
        ∑' i, ∫ t, f i t ∂μ) := by
  have hmass : (∑' i, ∫⁻ t, ‖f i t‖ₑ ∂μ) ≠ ⊤ := by
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    exact hs.tsum_ofReal_ne_top
  have hfinite : (∫⁻ t, ∑' i, ‖f i t‖ₑ ∂μ) ≠ ⊤ := by
    rwa [lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)]
  have hae : ∀ᵐ t ∂μ, Summable (fun i => ‖f i t‖) ∧ Summable (fun i => f i t) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum
      (fun i => (hf i).aestronglyMeasurable.enorm)) hfinite] with t ht
    have h := tsum_enorm_ne_top_iff_summable_norm.mp ht.ne
    exact ⟨h, h.of_norm⟩
  have hi : Integrable (fun t => ∑' i, f i t) μ := by
    refine ⟨AEStronglyMeasurable.tsum (fun i => (hf i).aestronglyMeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)) hfinite.lt_top
  have hn : Summable (fun i => ‖∫ t, f i t ∂μ‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  have he : (∫ t, ∑' i, f i t ∂μ) = ∑' i, ∫ t, f i t ∂μ :=
    (integral_tsum_of_summable_integral_norm hf hs).symm
  refine ⟨hae, hi, hn, he, ?_, ?_⟩
  · intro J e
    rw [show (fun t => ∑' j, f (e j) t) = (fun t => ∑' i, f i t) from
      funext (fun t => e.tsum_eq (fun i => f i t))]
    exact he
  · intro J g
    have hg := hn.of_norm.hasSum.tsum_fiberwise g
    exact ⟨summable_norm_iff.mpr hg.summable, hg.tsum_eq⟩

theorem diagonal_injective (A : SArithmeticData F) : Function.Injective A.diagonal := by
  intro x y h
  apply Units.ext
  let w : InfinitePlace F := Classical.choice inferInstance
  have hw := congrArg (fun g : A.G => ((g.1 w : w.Completion))) h
  exact (algebraMap F w.Completion).injective hw

def gamma1Hom (A : SArithmeticData F) : ProbeOrbitNormSum.Gamma A →* A.Gamma1 where
  toFun γ := ⟨⟨A.diagonal γ.val.val, A.Gamma_le_G1 (by
    obtain ⟨u, hu⟩ := γ.property
    change A.diagonal γ.val.val ∈ (A.U.map (powMonoidHom 6)).map A.diagonal
    apply Subgroup.mem_map.mpr
    refine ⟨γ.val.val, ?_, rfl⟩
    apply Subgroup.mem_map.mpr
    exact ⟨u.val, u.property, congrArg Subtype.val hu⟩)⟩, by
    change A.diagonal γ.val.val ∈ (A.U.map (powMonoidHom 6)).map A.diagonal
    obtain ⟨u, hu⟩ := γ.property
    exact Subgroup.mem_map.mpr ⟨γ.val.val, Subgroup.mem_map.mpr
      ⟨u.val, u.property, congrArg Subtype.val hu⟩, rfl⟩⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _

def gamma1Equiv (A : SArithmeticData F) : ProbeOrbitNormSum.Gamma A ≃* A.Gamma1 :=
  MulEquiv.ofBijective (gamma1Hom A) (by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact diagonal_injective A (congrArg (fun γ : A.Gamma1 => γ.val.val) h)
    · intro γ
      have hγ : γ.val.val ∈ (A.U.map (powMonoidHom 6)).map A.diagonal := γ.property
      obtain ⟨v, hv, heq⟩ := Subgroup.mem_map.mp hγ
      obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp hv
      let a : A.U := ⟨u, hu⟩
      let b : ProbeOrbitNormSum.Gamma A := ⟨a ^ 6, ⟨a, rfl⟩⟩
      refine ⟨b, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change A.diagonal (u ^ 6) = γ.val.val
      exact (congrArg A.diagonal huv).trans heq)

theorem orbit_regrouping {H G N O B : Type*}
    [MeasurableSpace H] [Group G] [MulAction G H] [MulAction G N]
    [Countable G] [Countable B] [Countable N] [Countable O]
    [MeasurableConstSMul G H]
    (μ : Measure H) [SMulInvariantMeasure G H μ]
    (D : Set H) (hD : IsFundamentalDomain G D μ)
    (ρ : O → N) (e : O × G ≃ N) (he : ∀ p, e p = p.2 • ρ p.1)
    (f : B → N → H → ℂ) (hm : ∀ b n, AEStronglyMeasurable (f b n) μ)
    (ht : ∀ b n (g : G) t, f b (g • n) t = f b n (g • t))
    (hi : ∀ p : B × N, IntegrableOn (f p.1 p.2) D μ)
    (hs : Summable (fun p : B × N => ∫ t in D, ‖f p.1 p.2 t‖ ∂μ)) :
    Summable (fun p : B × O => ‖∫ t, f p.1 (ρ p.2) t ∂μ‖) ∧
    Summable (fun p : B × O => ∫ t, f p.1 (ρ p.2) t ∂μ) ∧
    (∑' p : B × N, ∫ t in D, f p.1 p.2 t ∂μ) =
      ∑' p : B × O, ∫ t, f p.1 (ρ p.2) t ∂μ := by
  let E : (B × O) × G ≃ B × N :=
    (Equiv.prodAssoc B O G).trans (Equiv.prodCongr (Equiv.refl B) e)
  have hE (p : (B × O) × G) : E p = (p.1.1, p.2 • ρ p.1.2) := by
    simp [E, he]
  have hsE := hs.comp_injective E.injective
  have hInt (p : B × O) : Integrable (f p.1 (ρ p.2)) μ := by
    refine ⟨hm _ _, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    rw [hD.lintegral_eq_tsum'']
    have hsg : Summable (fun g : G => ∫ t in D, ‖f p.1 (g • ρ p.2) t‖ ∂μ) := by
      simpa only [Function.comp_def, hE] using hsE.prod_factor p
    have hn (g : G) : IntegrableOn (f p.1 (g • ρ p.2)) D μ := hi (p.1, g • ρ p.2)
    simp_rw [← ht p.1 (ρ p.2)]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hn _)]
    exact hsg.tsum_ofReal_ne_top.lt_top
  have hn : Summable (fun p : B × N => ‖∫ t in D, f p.1 p.2 t ∂μ‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  have hrow (p : B × O) :
      (∑' g : G, ∫ t in D, f p.1 (g • ρ p.2) t ∂μ) =
        ∫ t, f p.1 (ρ p.2) t ∂μ := by
    simp_rw [ht]
    exact (hD.integral_eq_tsum'' _ (hInt p)).symm
  have hf := hn.of_norm.comp_injective E.injective
  have hnorm : Summable (fun p : B × O => ‖∑' g : G,
      ∫ t in D, f p.1 (g • ρ p.2) t ∂μ‖) := by
    have hh := (hn.comp_injective E.injective).prod
    apply hh.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro p
    simpa only [Function.comp_def, hE] using
      norm_tsum_le_tsum_norm ((hn.comp_injective E.injective).prod_factor p)
  simp_rw [hrow] at hnorm
  refine ⟨hnorm, hnorm.of_norm, ?_⟩
  rw [← E.tsum_eq]
  calc
    _ = ∑' p : B × O, ∑' g : G,
        ((fun p : B × N => ∫ t in D, f p.1 p.2 t ∂μ) ∘ E) (p, g) := hf.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro p
      simpa only [Function.comp_def, hE] using hrow p

set_option maxHeartbeats 1000000 in
def blockEquiv (A : SArithmeticData F) (N : Type*) :
    (A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior) × N ≃
      A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior × N :=
  (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _))

set_option maxHeartbeats 1000000 in
theorem arithmetic_orbit_regrouping (A : SArithmeticData F)
    (D : NormalizedProbe.DomainData A)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : ProbeOrbitNormSum.IsRepresentativeSection A ρ)
    (f : Index A → A.G1 → ℂ)
    (hm : ∀ i, AEStronglyMeasurable (f i) D.measure)
    (ht : ∀ s c n h (γ : ProbeOrbitNormSum.Gamma A) t,
      f (s,c,n,γ • h) t = f (s,c,n,h) ((gamma1Equiv A γ).val * t))
    (hi : ∀ i, IntegrableOn (f i) D.domain D.measure)
    (hs : Summable (fun i => ∫ t in D.domain, ‖f i t‖ ∂D.measure)) :
    Summable (fun i : OrbitIndex A => ‖∫ t, f (i.1,i.2.1,i.2.2.1,ρ i.2.2.2) t ∂D.measure‖) ∧
    Summable (fun i : OrbitIndex A => ∫ t, f (i.1,i.2.1,i.2.2.1,ρ i.2.2.2) t ∂D.measure) ∧
    (∑' i : Index A, ∫ t in D.domain, f i t ∂D.measure) =
      ∑' i : OrbitIndex A, ∫ t, f (i.1,i.2.1,i.2.2.1,ρ i.2.2.2) t ∂D.measure := by
  have hcount := ProbeOrbitNormSum.indices_countable A
  letI : Countable (ProbeOrbitNormSum.Nonzero A) := hcount.1
  letI : Countable (ProbeOrbitNormSum.Gamma A) := hcount.2.2.1
  letI : Countable (ProbeOrbitNormSum.Orbit A) := hcount.2.2.2.2.1
  letI : Countable A.Exterior := hcount.2.2.2.2.2.1
  letI : Countable (ExteriorSquarefreeIdeal A.cS) := inferInstanceAs (Countable {I : A.Exterior // Squarefree I.val})
  letI := D.haar
  letI : MulAction (ProbeOrbitNormSum.Gamma A) A.G1 :=
    MulAction.compHom A.G1 (gamma1Equiv A).toMonoidHom
  letI : MeasurableConstSMul (ProbeOrbitNormSum.Gamma A) A.G1 := ⟨fun γ =>
    measurable_const_mul ((gamma1Equiv A γ).val)⟩
  letI : SMulInvariantMeasure (ProbeOrbitNormSum.Gamma A) A.G1 D.measure := by
    constructor
    intro γ s hs
    exact measure_preimage_mul D.measure ((gamma1Equiv A γ).val) s
  have hFD : IsFundamentalDomain (ProbeOrbitNormSum.Gamma A) D.domain D.measure := by
    apply IsFundamentalDomain.mk' D.measurable.nullMeasurableSet
    intro t
    obtain ⟨γ,hγ,hu⟩ := D.fundamental t
    refine ⟨(gamma1Equiv A).symm γ, ?_, ?_⟩
    · change (gamma1Equiv A ((gamma1Equiv A).symm γ)).val * t ∈ D.domain
      simpa using hγ
    · intro δ hδ
      apply (gamma1Equiv A).injective
      exact (hu _ hδ).trans (by simp)
  let e : ProbeOrbitNormSum.Orbit A × ProbeOrbitNormSum.Gamma A ≃ ProbeOrbitNormSum.Nonzero A :=
    Equiv.ofBijective _ (ProbeOrbitNormSum.sectionMultiply_bijective A ρ hρ)
  let B := A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior
  let fn : B → ProbeOrbitNormSum.Nonzero A → A.G1 → ℂ :=
    fun b h => f (b.1,b.2.1,b.2.2,h)
  let hb := blockEquiv A (ProbeOrbitNormSum.Nonzero A)
  let ho := blockEquiv A (ProbeOrbitNormSum.Orbit A)
  have hsr := hs.comp_injective hb.injective
  have hr := orbit_regrouping D.measure D.domain hFD ρ e (fun _ => rfl) fn
    (fun b h => hm _) (fun b h γ t => ht _ _ _ _ _ _)
    (fun p => hi _) (by simpa [fn, hb, blockEquiv, Function.comp_def] using hsr)
  refine ⟨?_, ?_, ?_⟩
  · simpa [fn, ho, blockEquiv, Function.comp_def] using hr.1.comp_injective ho.symm.injective
  · simpa [fn, ho, blockEquiv, Function.comp_def] using hr.2.1.comp_injective ho.symm.injective
  · rw [← hb.tsum_eq]
    refine hr.2.2.trans ?_
    simpa [fn, ho, blockEquiv] using ho.tsum_eq
      (fun i : OrbitIndex A => ∫ t, f (i.1,i.2.1,i.2.2.1,ρ i.2.2.2) t ∂D.measure)

theorem orbit_norm_unfolding_raw {H G N O B : Type*}
    [MeasurableSpace H] [Group G] [MulAction G H] [MulAction G N]
    [Countable G] [Countable B] [Countable N] [Countable O]
    [MeasurableConstSMul G H]
    (μ : Measure H) [SMulInvariantMeasure G H μ]
    (D : Set H) (hD : IsFundamentalDomain G D μ)
    (ρ : O → N) (e : O × G ≃ N) (he : ∀ p, e p = p.2 • ρ p.1)
    (f : B → N → H → ℝ≥0∞)
    (ht : ∀ b n (g : G) t, f b (g • n) t = f b n (g • t)) :
    (∑' p : B × N, ∫⁻ t in D, f p.1 p.2 t ∂μ) =
      ∑' p : B × O, ∫⁻ t, f p.1 (ρ p.2) t ∂μ := by
  let E : (B × O) × G ≃ B × N :=
    (Equiv.prodAssoc B O G).trans (Equiv.prodCongr (Equiv.refl B) e)
  have hE (p : (B × O) × G) : E p = (p.1.1, p.2 • ρ p.1.2) := by
    simp [E, he]
  rw [← E.tsum_eq]
  calc
    _ = ∑' p : B × O, ∑' g : G,
        ((fun q : B × N => ∫⁻ t in D, f q.1 q.2 t ∂μ) ∘ E) (p, g) := ENNReal.tsum_prod'
    _ = _ := by
      apply tsum_congr
      intro p
      simp only [Function.comp_def, hE, ht]
      exact (hD.lintegral_eq_tsum'' (f p.1 (ρ p.2))).symm

set_option maxHeartbeats 1000000 in

theorem norm_unfolding_raw (A : SArithmeticData F)
    (D : NormalizedProbe.DomainData A)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : ProbeOrbitNormSum.IsRepresentativeSection A ρ)
    (f : Index A → A.G1 → ℝ≥0∞)
    (ht : ∀ s c n h (γ : ProbeOrbitNormSum.Gamma A) t,
      f (s,c,n,γ • h) t = f (s,c,n,h) ((gamma1Equiv A γ).val * t))
    : (∑' i : Index A, ∫⁻ t in D.domain, f i t ∂D.measure) =
      ∑' i : OrbitIndex A, ∫⁻ t, f (i.1,i.2.1,i.2.2.1,ρ i.2.2.2) t ∂D.measure := by
  have hcount := ProbeOrbitNormSum.indices_countable A
  letI : Countable (ProbeOrbitNormSum.Nonzero A) := hcount.1
  letI : Countable (ProbeOrbitNormSum.Gamma A) := hcount.2.2.1
  letI : Countable (ProbeOrbitNormSum.Orbit A) := hcount.2.2.2.2.1
  letI : Countable A.Exterior := hcount.2.2.2.2.2.1
  letI : Countable (ExteriorSquarefreeIdeal A.cS) := inferInstanceAs (Countable {I : A.Exterior // Squarefree I.val})
  letI := D.haar
  letI : MulAction (ProbeOrbitNormSum.Gamma A) A.G1 :=
    MulAction.compHom A.G1 (gamma1Equiv A).toMonoidHom
  letI : MeasurableConstSMul (ProbeOrbitNormSum.Gamma A) A.G1 := ⟨fun γ =>
    measurable_const_mul ((gamma1Equiv A γ).val)⟩
  letI : SMulInvariantMeasure (ProbeOrbitNormSum.Gamma A) A.G1 D.measure := by
    constructor
    intro γ s hs
    exact measure_preimage_mul D.measure ((gamma1Equiv A γ).val) s
  have hFD : IsFundamentalDomain (ProbeOrbitNormSum.Gamma A) D.domain D.measure := by
    apply IsFundamentalDomain.mk' D.measurable.nullMeasurableSet
    intro t
    obtain ⟨γ,hγ,hu⟩ := D.fundamental t
    refine ⟨(gamma1Equiv A).symm γ, ?_, ?_⟩
    · change (gamma1Equiv A ((gamma1Equiv A).symm γ)).val * t ∈ D.domain
      simpa using hγ
    · intro δ hδ
      apply (gamma1Equiv A).injective
      exact (hu _ hδ).trans (by simp)
  let e : ProbeOrbitNormSum.Orbit A × ProbeOrbitNormSum.Gamma A ≃ ProbeOrbitNormSum.Nonzero A :=
    Equiv.ofBijective _ (ProbeOrbitNormSum.sectionMultiply_bijective A ρ hρ)
  let B := A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior
  let fn : B → ProbeOrbitNormSum.Nonzero A → A.G1 → ℝ≥0∞ :=
    fun b h => f (b.1,b.2.1,b.2.2,h)
  let hb := blockEquiv A (ProbeOrbitNormSum.Nonzero A)
  let ho := blockEquiv A (ProbeOrbitNormSum.Orbit A)
  have hr := orbit_norm_unfolding_raw D.measure D.domain hFD ρ e (fun _ => rfl) fn
    (fun b h γ t => ht _ _ _ _ _ _)
  rw [← hb.tsum_eq]
  refine hr.trans ?_
  simpa [fn, ho, blockEquiv] using ho.tsum_eq
    (fun i : OrbitIndex A => ∫⁻ t, f (i.1,i.2.1,i.2.2.1,ρ i.2.2.2) t ∂D.measure)

theorem gaussianMomentTerm_eq_doubleMomentSummand (A : SArithmeticData F)
    (σ Z : ℝ) :
    gaussianMomentTerm A σ Z =
      NormalizedProbe.gaussianDoubleMomentSummand A σ Z := by
  funext p
  simp only [gaussianMomentTerm, NormalizedProbe.gaussianDoubleMomentSummand,
    modulusNorm, Real.rpow_eq_pow]

theorem summable_gaussianMomentTerm (A : SArithmeticData F) (σ Z : ℝ)
    (hZ : 0 < Z) : Summable (gaussianMomentTerm A σ Z) := by
  rw [gaussianMomentTerm_eq_doubleMomentSummand]
  exact NormalizedProbe.gaussian_double_moments_summable A σ Z hZ

theorem summable_outerMoment (A : SArithmeticData F) (W1 : ProbeRealAnnularWeight)
    (Y : ℝ) (hY : 0 < Y) :
    Summable (fun s : A.Exterior =>
      |W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s) := by
  have hfin : ({s : A.Exterior | W1 (A.exteriorNorm s / Y) ≠ 0}).Finite :=
    NormalizedProbe.exterior_weight_finite A W1 Y hY
  refine summable_of_hasFiniteSupport (hfin.subset ?_)
  intro s hs
  simp only [Function.mem_support] at hs ⊢
  intro hW
  exact hs (by rw [hW, abs_zero, zero_mul])

theorem absoluteMass_of_joint_norm_summability (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS) (X Y Z : ℝ)
    (hi : ∀ i : Index A, IntegrableOn (kernel A ι η hS P X Y Z i)
      P.domain.domain P.domain.measure)
    (hs : Summable (fun i : Index A => ∫ t in P.domain.domain,
      ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure)) :
    absoluteMass A ι η hS P X Y Z < ⊤ ∧
    absoluteMass A ι η hS P X Y Z = ENNReal.ofReal
      (∑' i : Index A, ∫ t in P.domain.domain,
        ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure) := by
  have heq : absoluteMass A ι η hS P X Y Z =
      ∑' i : Index A, ENNReal.ofReal (∫ t in P.domain.domain,
        ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure) := by
    unfold absoluteMass
    apply tsum_congr
    intro i
    simpa only [← ofReal_norm] using
      (ofReal_integral_norm_eq_lintegral_enorm (hi i)).symm
  constructor
  · rw [heq]
    exact hs.tsum_ofReal_lt_top
  · rw [heq]
    have hnonneg (i : Index A) : 0 ≤ (∫ t in P.domain.domain,
        ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure) :=
      integral_nonneg (fun _ => norm_nonneg _)
    exact (ENNReal.ofReal_tsum_of_nonneg hnonneg hs).symm

theorem q_generator (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (s : A.Exterior) :
    ProbeSheetTranslation.q A (D.generator s) (D.generates s).1 = A.exteriorNorm s := by
  exact A.generator_norm s (D.generator s) (D.generates s)
    (ProbeSheetTranslation.fieldUnit A (D.generator s) (D.generates s).1) rfl

theorem frequency_eq_fractionPoint (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (X : ℝ) (hX : 0 < X)
    (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior)
    (h : ThetaReflectionData.Row A) :
    frequency A D X s c n h =
      (ProbeSheetTranslation.fractionPoint A X hX (D.generator s)
        (ThetaReflectionData.forwardModulus A D c n) h.val
        (D.generates s).1
        (mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)) h.property).val := by
  simp only [frequency, ProbeSheetTranslation.fractionPoint, q_generator]
  rw [mul_div_assoc]
  simp only [← map_mul, ← map_div, Units.val_mul]
  congr 1
  apply Prod.ext
  · funext w
    change (algebraMap F w.Completion) _ = (algebraMap F w.Completion) _
    simp [ProbeSheetTranslation.fieldUnit]
  · funext v
    change (algebraMap F (v.val.adicCompletion F)) _ =
      (algebraMap F (v.val.adicCompletion F)) _
    simp [ProbeSheetTranslation.fieldUnit]

theorem kernel_integrable (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A P.multiplicativeMeasure P.domain.measure)
    (X Y Z : ℝ) (hX : 0 < X) (i : Index A) :
    Integrable (kernel A ι η hS P X Y Z i) P.domain.measure := by
  obtain ⟨C, hC, hb⟩ := probe_sheet_shape_translation_fraction F A
    P.finiteTrace P.continuousTrace P.traceCompatible hne
    P.additiveMeasure P.multiplicativeMeasure P.domain.measure
    P.additiveHaar P.multiplicativeHaar P.domain.haar hnormalized
    (Classical.arbitrary _) P.W0 P.W1 P.annular P.compactSupport P.supportUnits
    2 (by norm_num)
  have ha := mul_ne_zero (P.coefficients.generates i.2.1.val).1
    (pow_ne_zero 3 (P.coefficients.generates i.2.2.1).1)
  have hi := (hb X hX (P.coefficients.generator i.1)
    (ThetaReflectionData.forwardModulus A P.coefficients i.2.1 i.2.2.1)
    i.2.2.2.val (P.coefficients.generates i.1).1 ha i.2.2.2.property).2.2.1
  have heq : (fun t : A.G1 => ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
      ((ProbeSheet.localUnits A t.val).val * frequency A P.coefficients X i.1 i.2.1 i.2.2.1 i.2.2.2)) =
      ProbeSheetTranslation.translatedFourier A P.finiteTrace P.additiveMeasure P.W0
      (ProbeSheetTranslation.fractionPoint A X hX (P.coefficients.generator i.1)
        (ThetaReflectionData.forwardModulus A P.coefficients i.2.1 i.2.2.1) i.2.2.2.val
        (P.coefficients.generates i.1).1 ha i.2.2.2.property) := by
    funext t
    rw [frequency_eq_fractionPoint A P.coefficients X hX]
    rfl
  unfold kernel
  exact (heq ▸ hi).const_mul _

private theorem norm_mul_raw (A : SArithmeticData F) (x y : A.G) :
    A.norm (x * y) = A.norm x * A.norm y := by
  simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    Units.val_mul, _root_.norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring
private theorem norm_pow_raw (A : SArithmeticData F) (x : A.G) (k : ℕ) :
    A.norm (x ^ k) = A.norm x ^ k := by
  induction k with
  | zero => simp [SArithmeticData.norm]
  | succ k hk => rw [pow_succ, norm_mul_raw, hk, pow_succ]
theorem q_forwardModulus (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    ProbeSheetTranslation.q A (ThetaReflectionData.forwardModulus A D c n)
      (mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)) = modulusNorm A c n := by
  let uc := ProbeSheetTranslation.fieldUnit A (D.generator c.val) (D.generates c.val).1
  let un := ProbeSheetTranslation.fieldUnit A (D.generator n) (D.generates n).1
  have hu : ProbeSheetTranslation.fieldUnit A (ThetaReflectionData.forwardModulus A D c n)
      (mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)) = uc * un ^ 3 := by
    apply Units.ext
    rfl
  unfold ProbeSheetTranslation.q
  rw [hu, map_mul, map_pow, norm_mul_raw, norm_pow_raw]
  exact congrArg₂ (fun x y : ℝ => x * y ^ 3) (q_generator A D c.val) (q_generator A D n)

theorem finiteCoefficient_norm_le (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (c : ExteriorSquarefreeIdeal A.cS) (n s : A.Exterior) (h : A.R) :
    ‖comparisonPoissonFiniteCoefficient F A P.coefficients c n s h‖ ≤
      A.exteriorNorm s * modulusNorm A c n := by
  let D := P.coefficients
  let a := ThetaReflectionData.forwardModulus A D c n
  have ha : a ≠ 0 := mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)
  letI := D.finiteResidue (D.generator s) (D.generates s).1
  letI := D.finiteResidue a ha
  have hsN : (FiniteTransform.exteriorNorm A.R.toSubring (D.generator s) : ℝ) = A.exteriorNorm s := by
    change (Nat.card (A.R ⧸ Ideal.span {D.generator s}) : ℝ) = _
    rw [(D.generates s).2, A.exteriorResidue_card]
    rfl
  have haN : (FiniteTransform.exteriorNorm A.R.toSubring a : ℝ) = modulusNorm A c n := by
    change ProbePoissonSheet.principalNorm A a = _
    rw [(ProbePoissonSheet.principalNorm_eq_modulus A a ha).1]
    exact q_forwardModulus A D c n
  have hp (x : F) : ‖D.additiveCharacter x‖ = 1 := by
    rw [P.sameTrace]
    simp [ProbeAdditive.phase, ProbeAdditive.archPhase, norm_mul, norm_prod, Complex.norm_exp]
  exact (FiniteTransform.finiteCoefficient_norm_le A.R.toSubring (D.generator s) a h
    (D.character (D.generator s)) (D.character a) D.additiveCharacter hp).trans_eq
    (congrArg₂ (fun x y : ℝ => x * y) hsN haN)

private theorem numeric_mass_bound (C X Y qc qn qs qh σ w g a : ℝ)
    (hC : 0 ≤ C) (hX : 0 < X) (hY : 0 < Y) (hc : 0 < qc) (hn : 0 < qn)
    (hs : 0 ≤ qs) (hh : 0 < qh) (hw : 0 ≤ w) (hg : 0 ≤ g) (ha : 0 ≤ a)
    (b d : ℝ) (hb : b ≤ qs * (qc * qn ^ 3))
    (hd : d ≤ C * (X * qh / (qc * qn ^ 3)) ^ (-σ)) (hd0 : 0 ≤ d) (hb0 : 0 ≤ b) :
    (Y⁻¹ * w * (a * g / (Real.sqrt qc * qn)) *
      (Real.sqrt X / (qc * qn ^ 3)) * b) * d ≤
      (C * Real.sqrt X * X ^ (-σ) / Y) * (w * qs) *
        (a / (Real.sqrt qc * qn) * (qc * qn ^ 3) ^ σ * g) * qh ^ (-σ) := by
  have hq : 0 < qc * qn ^ 3 := by positivity
  calc
    _ ≤ (Y⁻¹ * w * (a * g / (Real.sqrt qc * qn)) *
      (Real.sqrt X / (qc * qn ^ 3)) * (qs * (qc * qn ^ 3))) *
      (C * (X * qh / (qc * qn ^ 3)) ^ (-σ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hb (by positivity)
      · exact hd
      · exact hd0
      · positivity
    _ = _ := by
      rw [Real.div_rpow (mul_pos hX hh).le hq.le, Real.mul_rpow hX.le hh.le,
        Real.rpow_neg hq.le]
      field_simp
      <;> ring

theorem integrated_orbit_mass_bound (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A P.multiplicativeMeasure P.domain.measure)
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y →
      ∀ (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior)
        (h : ThetaReflectionData.Row A),
      (∫ t : A.G1, ‖kernel A ι η hS P X Y Z (s, c, n, h) t‖ ∂P.domain.measure) ≤
        (C * Real.sqrt X * X ^ (-σ) / Y) *
          (|P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s) *
          ProbePoissonGaussianRowBound.rowMass A P.coefficients σ Z c n *
          (ProbeSheetTranslation.q A h.val h.property) ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := probe_sheet_shape_translation_fraction F A
    P.finiteTrace P.continuousTrace P.traceCompatible hne
    P.additiveMeasure P.multiplicativeMeasure P.domain.measure
    P.additiveHaar P.multiplicativeHaar P.domain.haar hnormalized
    (Classical.arbitrary _) P.W0 P.W1 P.annular P.compactSupport P.supportUnits σ hσ
  refine ⟨C, hC, ?_⟩
  intro X Y Z hX hY s c n h
  let D := P.coefficients
  let a := ThetaReflectionData.forwardModulus A D c n
  have ha : a ≠ 0 := mul_ne_zero (D.generates c.val).1 (pow_ne_zero _ (D.generates n).1)
  have hb' := hb X hX (D.generator s) a h.val (D.generates s).1 ha h.property
  dsimp only at hb'
  have hqh : 0 < ProbeSheetTranslation.q A h.val h.property := by
    have hn := ProbePoissonSheet.principalNorm_eq_modulus A h.val h.property
    change 0 < A.norm (A.diagonal (ProbePoissonSheet.fieldUnit A h.val h.property))
    rw [← hn.1]
    exact hn.2
  have htranslate (t : A.G1) : ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
      ((ProbeSheet.localUnits A t.val).val * frequency A D X s c n h) =
      ProbeSheetTranslation.translatedFourier A P.finiteTrace P.additiveMeasure P.W0
        (ProbeSheetTranslation.fractionPoint A X hX (D.generator s) a h.val
          (D.generates s).1 ha h.property) t := by
    rw [frequency_eq_fractionPoint A D X hX]
    rfl
  have hnorm : (∫ t : A.G1, ‖kernel A ι η hS P X Y Z (s,c,n,h) t‖ ∂P.domain.measure) =
      (Y⁻¹ * |P.W1 (A.exteriorNorm s / Y)| *
        (‖ThetaReflectionData.forwardArithmeticWeight A D c n‖ *
          |thetaReflectionGaussian (modulusNorm A c n / Z)| /
          (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm n)) *
        (Real.sqrt X / modulusNorm A c n) *
        ‖comparisonPoissonFiniteCoefficient F A D c n s h.val‖) *
      (∫ t, ‖ProbeSheetTranslation.translatedFourier A P.finiteTrace P.additiveMeasure P.W0
        (ProbeSheetTranslation.fractionPoint A X hX (D.generator s) a h.val
          (D.generates s).1 ha h.property) t‖ ∂P.domain.measure) := by
    simp only [kernel, norm_mul, lambda, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hY, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_pos (A.exteriorNorm_pos n), abs_of_pos (mul_pos (A.exteriorNorm_pos c.val)
        (pow_pos (A.exteriorNorm_pos n) _)), abs_div,
      htranslate, modulusNorm]
    rw [integral_const_mul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY,
      abs_of_pos (A.exteriorNorm_pos c.val), abs_of_pos (pow_pos (A.exteriorNorm_pos n) 3)]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show P.coefficients = D from rfl, htranslate]
  rw [hnorm]
  have hbd := hb'.2.2.2.2.2
  rw [q_forwardModulus A D c n] at hbd
  exact numeric_mass_bound C X Y (A.exteriorNorm c.val) (A.exteriorNorm n)
    (A.exteriorNorm s) (ProbeSheetTranslation.q A h.val h.property) σ
    |P.W1 (A.exteriorNorm s / Y)| |thetaReflectionGaussian (modulusNorm A c n / Z)|
    ‖ThetaReflectionData.forwardArithmeticWeight A D c n‖ hC hX hY
    (A.exteriorNorm_pos c.val) (A.exteriorNorm_pos n) (A.exteriorNorm_pos s).le hqh
    (abs_nonneg _) (abs_nonneg _) (norm_nonneg _)
    _ _ (finiteCoefficient_norm_le A ι η hS P c n s h.val) hbd
    (integral_nonneg (fun _ => norm_nonneg _)) (norm_nonneg _)

set_option maxHeartbeats 1000000 in

theorem whole_group_orbit_mass_summable (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A P.multiplicativeMeasure P.domain.measure)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : ProbeOrbitNormSum.IsRepresentativeSection A ρ) :
    Summable (fun i : OrbitIndex A => ∫ t : A.G1,
      ‖kernel A ι η hS P X Y Z (i.1, i.2.1, i.2.2.1, ρ i.2.2.2) t‖ ∂P.domain.measure) := by
  obtain ⟨C, hC, hb⟩ := integrated_orbit_mass_bound A ι η hS P hne hnormalized 2 (by norm_num)
  obtain ⟨K, hK, hk⟩ := ProbePoissonGaussianRowBound.gaussian_row_domination A ι η hS 2 Z
    (by norm_num) hZ
  have hrow := (hk P).2.2.2.1
  have houter := summable_outerMoment A P.W1 Y hY
  have horbit := ProbeOrbitNormSum.orbit_norm_rpow_summable A 2 (by norm_num)
  have hr0 (p : ExteriorSquarefreeIdeal A.cS × A.Exterior) :
      0 ≤ ProbePoissonGaussianRowBound.rowMass A P.coefficients 2 Z p.1 p.2 := by
    unfold ProbePoissonGaussianRowBound.rowMass
    have hc := A.exteriorNorm_pos p.1.val
    have hn := A.exteriorNorm_pos p.2
    positivity
  have hf0 (s : A.Exterior) : 0 ≤ |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s :=
    mul_nonneg (abs_nonneg _) (A.exteriorNorm_pos s).le
  have ho0 (o : ProbeOrbitNormSum.Orbit A) : 0 ≤ (ProbeOrbitNormSum.orbitNorm A o) ^ (-(2:ℝ)) :=
    Real.rpow_nonneg (ProbeOrbitNormSum.orbitNorm_pos A o).le _
  have hproduct : Summable (fun i : A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
      (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
        ProbePoissonGaussianRowBound.rowMass A P.coefficients 2 Z i.2.1 i.2.2) :=
    summable_mul_of_summable_norm
      (f := fun s : A.Exterior => |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s)
      (g := fun p : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
        ProbePoissonGaussianRowBound.rowMass A P.coefficients 2 Z p.1 p.2)
      (by simpa only [Real.norm_of_nonneg (hf0 _)] using houter)
      (by simpa only [Real.norm_of_nonneg (hr0 _)] using hrow)
  have hproduct2 : Summable (fun i :
      (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) × ProbeOrbitNormSum.Orbit A =>
      ((|P.W1 (A.exteriorNorm i.1.1 / Y)| * A.exteriorNorm i.1.1) *
        ProbePoissonGaussianRowBound.rowMass A P.coefficients 2 Z i.1.2.1 i.1.2.2) *
        ProbeOrbitNormSum.orbitNorm A i.2 ^ (-(2:ℝ))) :=
    summable_mul_of_summable_norm
      (f := fun i : A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
        (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
          ProbePoissonGaussianRowBound.rowMass A P.coefficients 2 Z i.2.1 i.2.2)
      (g := fun o : ProbeOrbitNormSum.Orbit A => ProbeOrbitNormSum.orbitNorm A o ^ (-(2:ℝ)))
      (by simpa only [Real.norm_of_nonneg (mul_nonneg (hf0 _) (hr0 _))] using hproduct)
      (by simpa only [Real.norm_of_nonneg (ho0 _)] using horbit)
  let e : OrbitIndex A ≃ (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) ×
      ProbeOrbitNormSum.Orbit A :=
    { toFun := fun i => ((i.1, (i.2.1, i.2.2.1)), i.2.2.2)
      invFun := fun i => (i.1.1, i.1.2.1, i.1.2.2, i.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmajor : Summable (fun i : OrbitIndex A =>
      (C * Real.sqrt X * X ^ (-(2:ℝ)) / Y) *
        (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
        ProbePoissonGaussianRowBound.rowMass A P.coefficients 2 Z i.2.1 i.2.2.1 *
        ProbeOrbitNormSum.orbitNorm A i.2.2.2 ^ (-(2:ℝ))) := by
    have he := e.summable_iff.mpr hproduct2
    simpa only [e, Function.comp_apply, Equiv.coe_fn_mk, mul_assoc] using
      he.mul_left (C * Real.sqrt X * X ^ (-(2:ℝ)) / Y)
  apply hmajor.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  intro i
  have hq : ProbeSheetTranslation.q A (ρ i.2.2.2).val (ρ i.2.2.2).property =
      ProbeOrbitNormSum.orbitNorm A i.2.2.2 := by
    unfold ProbeSheetTranslation.q
    rw [← ProbeOrbitNormSum.orbitNorm_eq_snorm A (ρ i.2.2.2)
      (ProbeSheetTranslation.fieldUnit A _ _) rfl]
    rw [hρ i.2.2.2]
  simpa only [hq] using hb X Y Z hX hY i.1 i.2.1 i.2.2.1 (ρ i.2.2.2)

theorem orbit_integrals_absolutely_summable (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A P.multiplicativeMeasure P.domain.measure)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : ProbeOrbitNormSum.IsRepresentativeSection A ρ) :
    Summable (fun i : OrbitIndex A => ‖orbitIntegral A ι η hS P X Y Z ρ i‖) ∧
      Summable (orbitIntegral A ι η hS P X Y Z ρ) := by
  have hm := whole_group_orbit_mass_summable A ι η hS P hne hnormalized
    X Y Z hX hY hZ ρ hρ
  have hn : Summable (fun i : OrbitIndex A => ‖orbitIntegral A ι η hS P X Y Z ρ i‖) :=
    hm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  exact ⟨hn, hn.of_norm⟩

theorem frequency_gamma_translate (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (X : ℝ)
    (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior)
    (h : ThetaReflectionData.Row A) (γ : ProbeOrbitNormSum.Gamma A) :
    frequency A D X s c n (γ • h) =
      (ProbeSheet.localUnits A (gamma1Equiv A γ).val.val).val *
        frequency A D X s c n h := by
  have hval : ((gamma1Equiv A γ).val.val) = A.diagonal γ.val.val := rfl
  rw [hval]
  have hloc : (ProbeSheet.localUnits A (A.diagonal γ.val.val)).val =
      sLocalDiagonal F A.Sf (γ.val.val : F) := rfl
  rw [hloc]
  dsimp [frequency]
  rw [mul_left_comm]
  congr 1
  rw [← map_mul]
  congr 1
  change (((A.unitEquiv γ.val : A.R) * h.val : A.R) : F) / _ = _
  push_cast
  rw [mul_div_assoc]
  rfl

theorem fourier_gamma_translate (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (X : ℝ)
    (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior)
    (h : ThetaReflectionData.Row A) (γ : ProbeOrbitNormSum.Gamma A) (t : A.G1) :
    (ProbeSheet.localUnits A t.val).val * frequency A D X s c n (γ • h) =
      (ProbeSheet.localUnits A (((gamma1Equiv A γ).val * t).val)).val *
        frequency A D X s c n h := by
  rw [frequency_gamma_translate, ← mul_assoc]
  congr 1
  rw [Subgroup.coe_mul, map_mul, Units.val_mul, mul_comm]

theorem kernel_gamma_translate (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS) (X Y Z : ℝ)
    (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior)
    (h : ThetaReflectionData.Row A) (γ : ProbeOrbitNormSum.Gamma A) (t : A.G1) :
    kernel A ι η hS P X Y Z (s,c,n,γ • h) t =
      kernel A ι η hS P X Y Z (s,c,n,h) ((gamma1Equiv A γ).val * t) := by
  unfold kernel
  dsimp only
  rw [fourier_gamma_translate]
  congr 2
  exact ProbeJointNormMassTransfer.finiteCoefficient_gamma_invariant
    A ι η hS P c n s h.val γ

private theorem gaussian_nonneg (x : ℝ) : 0 ≤ thetaReflectionGaussian x := by
  unfold thetaReflectionGaussian
  split_ifs <;> positivity

theorem rowMass_le_gaussianMomentTerm (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS) (σ Z : ℝ)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    ProbePoissonGaussianRowBound.rowMass A P.coefficients σ Z c n ≤
      gaussianMomentTerm A σ Z (c,n) := by
  have htheta : ‖P.coefficients.theta (ThetaReflectionData.forwardModulus A P.coefficients c n)‖ = 1 := by
    let m : ThetaReflectionData.Row A :=
      ⟨ThetaReflectionData.forwardModulus A P.coefficients c n,
        mul_ne_zero (P.coefficients.generates c.val).1 (pow_ne_zero _ (P.coefficients.generates n).1)⟩
    exact (congrArg norm (P.theta_principal m)).trans (Circle.norm_coe _)
  have hw : ‖ThetaReflectionData.forwardArithmeticWeight A P.coefficients c n‖ ≤ 1 := by
    rw [ThetaReflectionData.forwardArithmeticWeight, norm_mul, htheta, mul_one]
    exact P.norm_gammaTwo_le_one A ι η hS c
  have hc := A.exteriorNorm_pos c.val
  have hn := A.exteriorNorm_pos n
  unfold ProbePoissonGaussianRowBound.rowMass gaussianMomentTerm modulusNorm
  rw [abs_of_nonneg (gaussian_nonneg _)]
  calc
    _ ≤ (1 / (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm n)) *
        (A.exteriorNorm c.val * A.exteriorNorm n ^ 3) ^ σ *
        thetaReflectionGaussian (A.exteriorNorm c.val * A.exteriorNorm n ^ 3 / Z) := by
      apply mul_le_mul_of_nonneg_right _ (gaussian_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right hw (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast (A.exteriorNorm n) 3,
        ← Real.rpow_mul hn.le, Real.sqrt_eq_rpow]
      norm_num only [Nat.cast_ofNat]
      rw [show (1 / (A.exteriorNorm c.val ^ (1/2:ℝ) * A.exteriorNorm n)) *
          (A.exteriorNorm c.val ^ σ * A.exteriorNorm n ^ ((3:ℝ)*σ)) =
        (A.exteriorNorm c.val ^ σ / A.exteriorNorm c.val ^ (1/2:ℝ)) *
          (A.exteriorNorm n ^ ((3:ℝ)*σ) / A.exteriorNorm n ^ (1:ℝ)) by
        rw [Real.rpow_one]; ring]
      rw [← Real.rpow_sub hc, ← Real.rpow_sub hn]

theorem orbit_mass_same_gaussian_majorant (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A P.multiplicativeMeasure P.domain.measure)
    (σ : ℝ) (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y Z : ℝ), 0 < X → 0 < Y → 0 < Z →
      ∀ (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A),
        ProbeOrbitNormSum.IsRepresentativeSection A ρ →
        (∑' i : OrbitIndex A, ∫ t : A.G1,
          ‖kernel A ι η hS P X Y Z (i.1, i.2.1, i.2.2.1, ρ i.2.2.2) t‖ ∂P.domain.measure) ≤
          C * ProbeOrbitNormSum.normPowerSum A σ * X ^ (1 / 2 - σ) / Y *
            outerMoment A P.W1 Y * gaussianMoment A σ Z := by
  obtain ⟨C, hC, hb⟩ := integrated_orbit_mass_bound A ι η hS P hne hnormalized σ (lt_trans zero_lt_one hσ)
  refine ⟨C, hC, ?_⟩
  intro X Y Z hX hY hZ ρ hρ
  have ho := ProbeOrbitNormSum.orbit_norm_rpow_summable A σ hσ
  have hr := summable_gaussianMomentTerm A σ Z hZ
  have hs := summable_outerMoment A P.W1 Y hY
  have ho0 (o : ProbeOrbitNormSum.Orbit A) : 0 ≤ ProbeOrbitNormSum.orbitNorm A o ^ (-σ) :=
    Real.rpow_nonneg (ProbeOrbitNormSum.orbitNorm_pos A o).le _
  have hgn (x : ℝ) : 0 ≤ thetaReflectionGaussian x := by
    unfold thetaReflectionGaussian
    split_ifs <;> positivity
  have hr0 (p : ExteriorSquarefreeIdeal A.cS × A.Exterior) :
      0 ≤ gaussianMomentTerm A σ Z p := by
    unfold gaussianMomentTerm
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (A.exteriorNorm_pos p.1.val).le _)
      (Real.rpow_nonneg (A.exteriorNorm_pos p.2).le _)) (hgn _)
  have hs0 (s : A.Exterior) : 0 ≤ |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s :=
    mul_nonneg (abs_nonneg _) (A.exteriorNorm_pos s).le
  let e : OrbitIndex A ≃ (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) ×
      ProbeOrbitNormSum.Orbit A :=
    { toFun := fun i => ((i.1, (i.2.1, i.2.2.1)), i.2.2.2)
      invFun := fun i => (i.1.1, i.1.2.1, i.1.2.2, i.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsr : Summable (fun i : A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
      (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
        gaussianMomentTerm A σ Z i.2) :=
    summable_mul_of_summable_norm
      (f := fun s : A.Exterior => |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s)
      (g := gaussianMomentTerm A σ Z)
      (by simpa only [Real.norm_of_nonneg (hs0 _)] using hs)
      (by simpa only [Real.norm_of_nonneg (hr0 _)] using hr)
  have hall : Summable (fun i : OrbitIndex A =>
      (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
        gaussianMomentTerm A σ Z (i.2.1, i.2.2.1) *
        ProbeOrbitNormSum.orbitNorm A i.2.2.2 ^ (-σ)) := by
    have hh : Summable (fun i :
        (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) × ProbeOrbitNormSum.Orbit A =>
        ((|P.W1 (A.exteriorNorm i.1.1 / Y)| * A.exteriorNorm i.1.1) *
          gaussianMomentTerm A σ Z i.1.2) *
          ProbeOrbitNormSum.orbitNorm A i.2 ^ (-σ)) :=
      summable_mul_of_summable_norm
        (f := fun i : A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
          (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
            gaussianMomentTerm A σ Z i.2)
        (g := fun o => ProbeOrbitNormSum.orbitNorm A o ^ (-σ))
        (by simpa only [Real.norm_of_nonneg (mul_nonneg (hs0 _) (hr0 _))] using hsr)
        (by simpa only [Real.norm_of_nonneg (ho0 _)] using ho)
    simpa only [Function.comp_def, e, Equiv.coe_fn_mk, mul_assoc] using
      e.summable_iff.mpr hh
  have hmajor : Summable (fun i : OrbitIndex A =>
      (C * Real.sqrt X * X ^ (-σ) / Y) *
        (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
          gaussianMomentTerm A σ Z (i.2.1, i.2.2.1) *
            ProbeOrbitNormSum.orbitNorm A i.2.2.2 ^ (-σ)) := by
    simpa only [mul_assoc] using hall.mul_left (C * Real.sqrt X * X ^ (-σ) / Y)
  have hm := whole_group_orbit_mass_summable A ι η hS P hne hnormalized X Y Z hX hY hZ ρ hρ
  calc
    _ ≤ ∑' i : OrbitIndex A, (C * Real.sqrt X * X ^ (-σ) / Y) *
        (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
          gaussianMomentTerm A σ Z (i.2.1, i.2.2.1) *
            ProbeOrbitNormSum.orbitNorm A i.2.2.2 ^ (-σ) := by
      apply hm.tsum_le_tsum _ hmajor
      intro i
      have hq : ProbeSheetTranslation.q A (ρ i.2.2.2).val (ρ i.2.2.2).property =
          ProbeOrbitNormSum.orbitNorm A i.2.2.2 := by
        unfold ProbeSheetTranslation.q
        rw [← ProbeOrbitNormSum.orbitNorm_eq_snorm A (ρ i.2.2.2)
          (ProbeSheetTranslation.fieldUnit A _ _) rfl, hρ i.2.2.2]
      have hrow := rowMass_le_gaussianMomentTerm A ι η hS P σ Z i.2.1 i.2.2.1
      exact (hb X Y Z hX hY i.1 i.2.1 i.2.2.1 (ρ i.2.2.2)).trans <| by
        simp only [hq]
        apply mul_le_mul_of_nonneg_right _ (ho0 _)
        apply mul_le_mul_of_nonneg_left hrow
        exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg X))
          (Real.rpow_nonneg hX.le _)) hY.le) (hs0 _)
    _ = _ := by
      simp_rw [show C * Real.sqrt X * X ^ (-σ) = C * (Real.sqrt X * X ^ (-σ)) by ring]
      rw [show Real.sqrt X * X ^ (-σ) = X ^ (1 / 2 - σ) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX]
        congr 1]
      simp_rw [mul_assoc, tsum_mul_left]
      have heq : (∑' i : OrbitIndex A,
          (|P.W1 (A.exteriorNorm i.1 / Y)| * A.exteriorNorm i.1) *
            gaussianMomentTerm A σ Z (i.2.1, i.2.2.1) *
            ProbeOrbitNormSum.orbitNorm A i.2.2.2 ^ (-σ)) =
          outerMoment A P.W1 Y * gaussianMoment A σ Z * ProbeOrbitNormSum.normPowerSum A σ := by
        rw [← e.symm.tsum_eq]
        change (∑' i : (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) ×
          ProbeOrbitNormSum.Orbit A, (|P.W1 (A.exteriorNorm i.1.1 / Y)| * A.exteriorNorm i.1.1) *
            gaussianMomentTerm A σ Z i.1.2 * ProbeOrbitNormSum.orbitNorm A i.2 ^ (-σ)) = _
        have hprod := hsr.tsum_mul_tsum ho (e.summable_iff.mp hall)
        rw [← hprod]
        rw [← hs.tsum_mul_tsum hr hsr]
        rfl
      simp_rw [mul_assoc] at heq
      rw [heq]
      ring

theorem finite_absolute_mass (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A
      P.multiplicativeMeasure P.domain.measure)
    (σ : ℝ) (hσ : 1 < σ) :
    ∃ Cσ : ℝ, 0 ≤ Cσ ∧ ∀ (X Y Z : ℝ), 0 < X → 0 < Y → 0 < Z →
      (∀ i : Index A, IntegrableOn (kernel A ι η hS P X Y Z i)
        P.domain.domain P.domain.measure) ∧
      Summable (fun i : Index A => ∫ t in P.domain.domain,
        ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure) ∧
      absoluteMass A ι η hS P X Y Z < ⊤ ∧
      absoluteMass A ι η hS P X Y Z = ENNReal.ofReal
        (∑' i : Index A, ∫ t in P.domain.domain,
          ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure) ∧
      (∑' i : Index A, ∫ t in P.domain.domain,
        ‖kernel A ι η hS P X Y Z i t‖ ∂P.domain.measure) ≤
          Cσ * ProbeOrbitNormSum.normPowerSum A σ * X ^ (1 / 2 - σ) / Y *
            outerMoment A P.W1 Y * gaussianMoment A σ Z ∧
      {s : A.Exterior | P.W1 (A.exteriorNorm s / Y) ≠ 0}.Finite ∧
      Summable (fun s : A.Exterior =>
        |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s) ∧
      Summable (gaussianMomentTerm A σ Z) := by
  obtain ⟨C, hC, hb⟩ := orbit_mass_same_gaussian_majorant A ι η hS P hne hnormalized σ hσ
  refine ⟨C, hC, ?_⟩
  intro X Y Z hX hY hZ
  let ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A := Quotient.out
  have hρ : ProbeOrbitNormSum.IsRepresentativeSection A ρ := by
    intro o
    exact Quotient.out_eq o
  have hiG := kernel_integrable A ι η hS P hne hnormalized X Y Z hX
  have hi : ∀ i : Index A, IntegrableOn (kernel A ι η hS P X Y Z i)
      P.domain.domain P.domain.measure := fun i => (hiG i).integrableOn
  have ho := whole_group_orbit_mass_summable A ι η hS P hne hnormalized
    X Y Z hX hY hZ ρ hρ
  have he := norm_unfolding_raw A P.domain ρ hρ
    (fun i t => ENNReal.ofReal ‖kernel A ι η hS P X Y Z i t‖)
    (fun s c n h γ t => congrArg (fun z : ℂ => ENNReal.ofReal ‖z‖)
      (kernel_gamma_translate A ι η hS P X Y Z s c n h γ t))
  obtain ⟨hs, hsum⟩ := ProbeJointNormMassTransfer.norm_mass_transfer
    P.domain.measure P.domain.domain (kernel A ι η hS P X Y Z)
    (fun (i : OrbitIndex A) => kernel A ι η hS P X Y Z
      (i.1,i.2.1,i.2.2.1,ρ i.2.2.2)) hi (fun i => hiG _) ho he
  obtain ⟨hfinite, hmass⟩ := absoluteMass_of_joint_norm_summability A ι η hS P X Y Z hi hs
  refine ⟨hi, hs, hfinite, hmass, ?_,
    NormalizedProbe.exterior_weight_finite A P.W1 Y hY,
    summable_outerMoment A P.W1 Y hY, summable_gaussianMomentTerm A σ Z hZ⟩
  rw [hsum]
  exact hb X Y Z hX hY hZ ρ hρ

theorem exchanges_and_orbit_convergence (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A
      P.multiplicativeMeasure P.domain.measure)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (∀ᵐ t ∂P.domain.measure.restrict P.domain.domain,
      Summable (fun i : Index A => ‖kernel A ι η hS P X Y Z i t‖) ∧
      Summable (fun i : Index A => kernel A ι η hS P X Y Z i t)) ∧
    IntegrableOn (fun t => ∑' i : Index A, kernel A ι η hS P X Y Z i t)
      P.domain.domain P.domain.measure ∧
    Summable (fun i : Index A =>
      ‖∫ t in P.domain.domain, kernel A ι η hS P X Y Z i t ∂P.domain.measure‖) ∧
    (∫ t in P.domain.domain, ∑' i : Index A, kernel A ι η hS P X Y Z i t
      ∂P.domain.measure) =
      ∑' i : Index A, ∫ t in P.domain.domain,
        kernel A ι η hS P X Y Z i t ∂P.domain.measure ∧
    (∀ (J : Type) (e : J ≃ Index A),
      (∫ t in P.domain.domain, ∑' j : J, kernel A ι η hS P X Y Z (e j) t
        ∂P.domain.measure) =
        ∑' i : Index A, ∫ t in P.domain.domain,
          kernel A ι η hS P X Y Z i t ∂P.domain.measure) ∧
    (∀ (J : Type) (g : Index A → J),
      Summable (fun j : J =>
        ‖∑' i : {i : Index A // g i = j}, ∫ t in P.domain.domain,
          kernel A ι η hS P X Y Z i.val t ∂P.domain.measure‖) ∧
      (∑' j : J, ∑' i : {i : Index A // g i = j}, ∫ t in P.domain.domain,
        kernel A ι η hS P X Y Z i.val t ∂P.domain.measure) =
        ∑' i : Index A, ∫ t in P.domain.domain,
          kernel A ι η hS P X Y Z i t ∂P.domain.measure) ∧
    (∀ (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A),
      ProbeOrbitNormSum.IsRepresentativeSection A ρ →
        Summable (fun i : OrbitIndex A => ‖orbitIntegral A ι η hS P X Y Z ρ i‖) ∧
        Summable (orbitIntegral A ι η hS P X Y Z ρ) ∧
        (∫ t in P.domain.domain, ∑' i : Index A, kernel A ι η hS P X Y Z i t
          ∂P.domain.measure) =
          ∑' i : OrbitIndex A, orbitIntegral A ι η hS P X Y Z ρ i) := by
  have hcount := ProbeOrbitNormSum.indices_countable A
  letI : Countable (ProbeOrbitNormSum.Nonzero A) := hcount.1
  letI : Countable A.Exterior := hcount.2.2.2.2.2.1
  letI : Countable (ExteriorSquarefreeIdeal A.cS) :=
    inferInstanceAs (Countable {I : A.Exterior // Squarefree I.val})
  obtain ⟨C, hC, hscales⟩ := finite_absolute_mass A ι η hS P hne hnormalized 2 (by norm_num)
  obtain ⟨hi, hs, _⟩ := hscales X Y Z hX hY hZ
  obtain ⟨hae, hint, hn, heq, hreindex, hfibers⟩ := joint_series_exchanges
    (P.domain.measure.restrict P.domain.domain) (kernel A ι η hS P X Y Z) hi hs
  refine ⟨hae, hint, hn, heq, hreindex, hfibers, ?_⟩
  intro ρ hρ
  have hr := arithmetic_orbit_regrouping A P.domain ρ hρ
    (kernel A ι η hS P X Y Z)
    (fun i => (kernel_integrable A ι η hS P hne hnormalized X Y Z hX i).aestronglyMeasurable)
    (fun s c n h γ t => kernel_gamma_translate A ι η hS P X Y Z s c n h γ t)
    hi hs
  exact ⟨hr.1, hr.2.1, heq.trans hr.2.2⟩

end
end ProbeJointAbsoluteMass
end DedekindZetaZeroFree
