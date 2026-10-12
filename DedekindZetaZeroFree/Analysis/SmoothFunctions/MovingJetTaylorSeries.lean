module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordFiniteSums
public import DedekindZetaZeroFree.Analysis.Analytic.SmoothSeries.ScalarMultiplication
public import DedekindZetaZeroFree.Eisenstein.Continuation.ChamberSeries.SpatialDifferentiation
public import DedekindZetaZeroFree.Theta.Periods.CompactKernelOrbitData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open KPGlobalResidualConstruction KPGlobalEisensteinData
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming finite_level_exists → finite_level_exists
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def nativeSmoothSpace : Submodule ℂ (KPLiteralRaw.Functions F ζ hζ) where
  carrier := {f | KPLiteralRaw.Smooth F ζ hζ f}
  zero_mem' := by
    obtain ⟨U⟩ := finite_level_exists F ζ hζ
    exact smooth_zero F ζ hζ U
  add_mem' := fun hf hg => smooth_add F ζ hζ _ _ hf hg
  smul_mem' := fun c _ hf => smooth_smul F ζ hζ c _ hf

def movingJetMap (j : G F ζ hζ × Jet F) :
    nativeSmoothSpace F ζ hζ →ₗ[ℂ] C(archDomain F, ℂ) where
  toFun f := ⟨fun x => iteratedFDeriv ℝ j.2.1
    (fun y => f.val (j.1 * archChart F ζ hζ y)) x.val j.2.2, by
      let u := fun y => f.val (j.1 * archChart F ζ hζ y)
      have hu : ContDiffOn ℝ (⊤ : ℕ∞) u (archDomain F) := f.property.2.1 j.1
      have hD := ActualDifferentialData.archDomain_isOpen F
      have hc := hu.continuousOn_iteratedFDerivWithin (m := j.2.1) (by simp) hD.uniqueDiffOn
      have he : ContinuousOn (fun x => iteratedFDeriv ℝ j.2.1 u x) (archDomain F) :=
        hc.congr (fun x hx => (iteratedFDerivWithin_of_isOpen j.2.1 hD hx).symm)
      exact (continuous_eval_const j.2.2).comp
        (continuousOn_iff_continuous_restrict.mp he)⟩
  map_add' f k := by
    ext x
    have hD := ActualDifferentialData.archDomain_isOpen F
    have hf : ContDiffAt ℝ j.2.1 (fun y => f.val (j.1 * archChart F ζ hζ y)) x.val :=
      ((f.property.2.1 j.1).contDiffAt (hD.mem_nhds x.property)).of_le (by simp)
    have hk : ContDiffAt ℝ j.2.1 (fun y => k.val (j.1 * archChart F ζ hζ y)) x.val :=
      ((k.property.2.1 j.1).contDiffAt (hD.mem_nhds x.property)).of_le (by simp)
    change iteratedFDeriv ℝ j.2.1
      ((fun y => f.val (j.1 * archChart F ζ hζ y)) +
        (fun y => k.val (j.1 * archChart F ζ hζ y))) x.val j.2.2 = _
    rw [iteratedFDeriv_add_apply hf hk, ContinuousMultilinearMap.add_apply]
    rfl
  map_smul' c f := by
    ext x
    have hD := ActualDifferentialData.archDomain_isOpen F
    have hf : ContDiffAt ℝ j.2.1 (fun y => f.val (j.1 * archChart F ζ hζ y)) x.val :=
      ((f.property.2.1 j.1).contDiffAt (hD.mem_nhds x.property)).of_le (by simp)
    change iteratedFDeriv ℝ j.2.1
      (c • (fun y => f.val (j.1 * archChart F ζ hζ y))) x.val j.2.2 = _
    rw [iteratedFDeriv_const_smul_apply (a := c) hf, ContinuousMultilinearMap.smul_apply]
    rfl

theorem movingJet_powerSeries_of_compact_taylor
    (b : ℕ → nativeSmoothSpace F ζ hζ) (N : ℂ → nativeSmoothSpace F ζ hζ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (ht : ∀ (g : G F ζ hζ) (m : ℕ) (K : Set (ArchCoordinates F)),
      IsCompact K → K ⊆ archDomain F → ∀ r : ℝ, 0 < r → r < ρ →
      ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ M ≥ k, ∀ s : ℂ, ‖s‖ ≤ r → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => (N s).val (g * archChart F ζ hζ y) -
          ∑ n ∈ Finset.range M, s ^ n * (b n).val (g * archChart F ζ hζ y)) x‖ < ε) :
    SmoothPowerSeriesOn (movingJetMap F ζ hζ) 0 ρ b N := by
  intro i r hr hrρ ε hε
  let K := Subtype.val '' i.compact
  have hK : IsCompact K := i.isCompact.image continuous_subtype_val
  have hKd : K ⊆ archDomain F := by rintro _ ⟨x, hx, rfl⟩; exact x.property
  let t := (r+ρ)/2
  have ht0 : 0 < t := by dsimp [t]; linarith
  have hrt : r < t := by dsimp [t]; linarith
  have htρ : t < ρ := by dsimp [t]; linarith
  let B : ℝ := ∏ j : Fin i.operator.2.1, ‖i.operator.2.2 j‖
  have hB : 0 ≤ B := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  let δ := ε / (2 * (B+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨k, hk⟩ := ht i.operator.1 i.operator.2.1 K hK hKd t ht0 htρ δ hδ
  refine ⟨k, ?_⟩
  intro M hM s hs
  change ‖derivativeRestriction (movingJetMap F ζ hζ) i
    ((∑ n ∈ Finset.range M, (s-0)^n • b n) - N s)‖ < ε
  apply lt_of_le_of_lt ((ContinuousMap.norm_le _ (by positivity : 0 ≤ ε/2)).mpr ?_)
    (half_lt_self hε)
  intro x
  let u := fun y => (N s).val (i.operator.1 * archChart F ζ hζ y) -
    ∑ n ∈ Finset.range M, s ^ n * (b n).val (i.operator.1 * archChart F ζ hζ y)
  have he : (fun y =>
      (((∑ n ∈ Finset.range M, (s-0)^n • b n) - N s) : nativeSmoothSpace F ζ hζ).val
        (i.operator.1 * archChart F ζ hζ y)) = -u := by
    funext y
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, sub_zero, smul_eq_mul, u, Pi.neg_apply]
    ring
  change ‖iteratedFDeriv ℝ i.operator.2.1 _ x.val.val i.operator.2.2‖ ≤ ε/2
  rw [he, iteratedFDeriv_neg]
  simp only [Pi.neg_apply, ContinuousMultilinearMap.neg_apply, norm_neg]
  have hu := hk M hM s ((by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hs : ‖s‖ ≤ r).trans hrt.le)
    x.val.val ⟨x.val, x.property, rfl⟩
  have hop := (iteratedFDeriv ℝ i.operator.2.1 u x.val.val).le_opNorm i.operator.2.2
  have hh : ‖iteratedFDeriv ℝ i.operator.2.1 u x.val.val‖ < δ := hu
  have hb : ‖iteratedFDeriv ℝ i.operator.2.1 u x.val.val‖ * B ≤ δ * B :=
    mul_le_mul_of_nonneg_right hh.le hB
  have hδε : δ * (2*(B+1)) = ε := by dsimp [δ]; field_simp
  exact hop.trans (by change _ ≤ ε/2; nlinarith)

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalChamberSpatialInsertion renaming basis_jet_norm_bound → basis_jet_norm_bound

theorem compact_taylor_of_movingJet_powerSeries
    (b : ℕ → nativeSmoothSpace F ζ hζ) (N : ℂ → nativeSmoothSpace F ζ hζ)
    (ρ : ℝ) (ht : SmoothPowerSeriesOn (movingJetMap F ζ hζ) 0 ρ b N)
    (g : G F ζ hζ) (m : ℕ) (K : Set (ArchCoordinates F))
    (hK : IsCompact K) (hKd : K ⊆ archDomain F) (r : ℝ) (hr : 0 < r) (hrρ : r < ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ M ≥ k, ∀ s : ℂ, ‖s‖ ≤ r → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun y => (N s).val (g * archChart F ζ hζ y) -
        ∑ n ∈ Finset.range M, s ^ n * (b n).val (g * archChart F ζ hζ y)) x‖ < ε := by
  let e := Module.finBasis ℝ (ArchCoordinates F)
  let T := Fin m → Fin (Module.finrank ℝ (ArchCoordinates F))
  obtain ⟨A, hA, hbound⟩ := basis_jet_norm_bound m e
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let p : K → archDomain F := fun x => ⟨x.val, hKd x.property⟩
  have hp : Continuous p := continuous_subtype_val.subtype_mk _
  let L := Set.range p
  have hL : IsCompact L := isCompact_range hp
  let i : T → DifferentialCompact (archDomain F) (G F ζ hζ × Jet F) :=
    fun t => ⟨L, hL, g, m, fun j => e (t j)⟩
  let δ := ε / (2 * (A+1) * (Fintype.card T + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose k hk using (fun t : T => ht (i t) r hr.le hrρ δ hδ)
  refine ⟨Finset.univ.sup k, ?_⟩
  intro M hM s hs x hx
  let u := fun y => (N s).val (g * archChart F ζ hζ y) -
    ∑ n ∈ Finset.range M, s ^ n * (b n).val (g * archChart F ζ hζ y)
  have he : (fun y =>
      (((∑ n ∈ Finset.range M, (s-0)^n • b n) - N s) : nativeSmoothSpace F ζ hζ).val
        (g * archChart F ζ hζ y)) = -u := by
    funext y
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, sub_zero, smul_eq_mul, u, Pi.neg_apply]
    ring
  have hb (t : T) : ‖iteratedFDeriv ℝ m u x (fun j => e (t j))‖ ≤ δ := by
    letI : CompactSpace (i t).compact := isCompact_iff_compactSpace.mp (i t).isCompact
    have h := hk t M ((Finset.le_sup (Finset.mem_univ t)).trans hM) s
      (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hs)
    have hpL : p ⟨x,hx⟩ ∈ L := ⟨⟨x,hx⟩, rfl⟩
    have hv := (derivativeRestriction (movingJetMap F ζ hζ) (i t)
      ((∑ n ∈ Finset.range M, (s-0)^n • b n) - N s)).norm_coe_le_norm
        ⟨p ⟨x,hx⟩, hpL⟩
    change ‖iteratedFDeriv ℝ m _ x (fun j => e (t j))‖ ≤ _ at hv
    rw [he, iteratedFDeriv_neg] at hv
    simp only [Pi.neg_apply, ContinuousMultilinearMap.neg_apply, norm_neg] at hv
    exact (hv.trans_lt h).le
  have hsum : (∑ t : T, ‖iteratedFDeriv ℝ m u x (fun j => e (t j))‖) ≤ Fintype.card T * δ := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (f := fun t : T =>
        ‖iteratedFDeriv ℝ m u x (fun j => e (t j))‖) (g := fun _ => δ) (fun t _ => hb t))
  have hδe : δ * (2*(A+1)*(Fintype.card T+1)) = ε := by dsimp [δ]; field_simp
  have hc : 0 ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  have hsmall : A * (Fintype.card T * δ) < ε := by nlinarith
  exact (hbound _).trans_lt ((mul_le_mul_of_nonneg_left hsum hA).trans_lt hsmall)

end DedekindZetaZeroFree.SharedSource

end
