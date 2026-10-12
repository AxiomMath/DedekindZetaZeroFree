module

public import DedekindZetaZeroFree.Analysis.IsolatedSpectralProjections
public import DedekindZetaZeroFree.Analysis.OperatorTheory.Resolvents.ShiftedPencilHolomorphy

@[expose] public section

namespace DedekindZetaZeroFree.KPIsolatedLaurent

noncomputable section

open Filter Topology

def poleLocation (β : ℝ) : ℝ := β⁻¹ - 1

def complementProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (β : ℝ) : H →L[ℂ] H :=
  1 - KPIsolatedProjection.projection B β

def correctedPencil
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (β : ℝ) (z : ℂ) : H →L[ℂ] H :=
  KPResolventPencil.shiftedPencil B z + KPIsolatedProjection.projection B β

def holomorphicComplement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (β : ℝ) (z : ℂ) : H →L[ℂ] H :=
  B * complementProjection B β * Ring.inverse (correctedPencil B β z) *
    complementProjection B β

private lemma pencil_decomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (β : ℝ) (hβ : β ≠ 0) (z : ℂ)
    (hz : z ≠ (poleLocation β : ℂ))
    (hPP : KPIsolatedProjection.projection B β * KPIsolatedProjection.projection B β =
      KPIsolatedProjection.projection B β)
    (hBP : B * KPIsolatedProjection.projection B β =
      (β : ℂ) • KPIsolatedProjection.projection B β)
    (hPB : KPIsolatedProjection.projection B β * B =
      (β : ℂ) • KPIsolatedProjection.projection B β)
    (ht : IsUnit (correctedPencil B β z)) :
    IsUnit (KPResolventPencil.shiftedPencil B z) ∧
      KPResolventPencil.shiftedResolvent B z =
        ((poleLocation β : ℂ) - z)⁻¹ • KPIsolatedProjection.projection B β +
          holomorphicComplement B β z := by
  let P := KPIsolatedProjection.projection B β
  let Q := complementProjection B β
  let A := KPResolventPencil.shiftedPencil B z
  let T := correctedPencil B β z
  let V := Ring.inverse T
  let a : ℂ := 1 - (z + 1) * (β : ℂ)
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have haform : a = (β : ℂ) * ((poleLocation β : ℂ) - z) := by
    dsimp [a, poleLocation]
    push_cast
    field_simp
    <;> ring
  have ha : a ≠ 0 := by
    rw [haform]
    exact mul_ne_zero hβc (sub_ne_zero.mpr hz.symm)
  have hQQ : Q * Q = Q := by
    dsimp [Q, complementProjection]
    noncomm_ring [hPP]
  have hPQ : P * Q = 0 := by
    dsimp [P, Q, complementProjection]
    rw [mul_sub, mul_one, hPP, sub_self]
  have hQP : Q * P = 0 := by
    dsimp [P, Q, complementProjection]
    rw [sub_mul, one_mul, hPP, sub_self]
  have hAP : A * P = a • P := by
    dsimp [A, P, a, KPResolventPencil.shiftedPencil]
    rw [sub_mul, one_mul, smul_mul_assoc, hBP, smul_smul]
    first | module
  have hPA : P * A = a • P := by
    dsimp [A, P, a, KPResolventPencil.shiftedPencil]
    rw [mul_sub, mul_one, mul_smul_comm, hPB, smul_smul]
    first | module
  have hT : T = A + P := rfl
  have hTV : T * V = 1 := Ring.mul_inverse_cancel T ht
  have hVT : V * T = 1 := Ring.inverse_mul_cancel T ht
  have hTQ : T * Q = Q * T := by
    dsimp [Q, complementProjection]
    change T * (1 - P) = (1 - P) * T
    rw [mul_sub, sub_mul, mul_one, one_mul, hT, add_mul, mul_add, hAP, hPA]
  have hQV : Q * V = V * Q := by
    calc
      Q * V = (V * T) * Q * V := by rw [hVT, one_mul]
      _ = V * (T * Q) * V := by simp only [mul_assoc]
      _ = V * (Q * T) * V := by rw [hTQ]
      _ = V * Q := by rw [mul_assoc, mul_assoc, hTV, mul_one]
  have hAQ : A * Q = T * Q := by rw [hT, add_mul, hPQ, add_zero]
  have hQA : Q * A = Q * T := by rw [hT, mul_add, hQP, add_zero]
  have hAC : A * (Q * V * Q) = Q := by
    calc
      A * (Q * V * Q) = (A * Q) * V * Q := by simp only [mul_assoc]
      _ = (T * Q) * V * Q := by rw [hAQ]
      _ = (Q * T) * V * Q := by rw [hTQ]
      _ = Q * Q := by rw [mul_assoc Q T V, hTV, mul_one]
      _ = Q := hQQ
  have hCA : (Q * V * Q) * A = Q := by
    calc
      (Q * V * Q) * A = Q * V * (Q * A) := by simp only [mul_assoc]
      _ = Q * V * (Q * T) := by rw [hQA]
      _ = Q * V * (T * Q) := by rw [hTQ]
      _ = Q * Q := by rw [mul_assoc Q V (T * Q), ← mul_assoc V T Q, hVT, one_mul]
      _ = Q := hQQ
  let C := a⁻¹ • P + Q * V * Q
  have hAC' : A * C = 1 := by
    dsimp [C]
    rw [mul_add, mul_smul_comm, hAP, smul_smul, inv_mul_cancel₀ ha, one_smul, hAC]
    dsimp [P, Q, complementProjection]
    abel
  have hCA' : C * A = 1 := by
    dsimp [C]
    rw [add_mul, smul_mul_assoc, hPA, smul_smul, inv_mul_cancel₀ ha, one_smul, hCA]
    dsimp [P, Q, complementProjection]
    abel
  have hu : IsUnit A := isUnit_iff_exists.mpr ⟨C, hAC', hCA'⟩
  have hi : Ring.inverse A = C := by
    calc
      Ring.inverse A = Ring.inverse A * (A * C) := by rw [hAC', mul_one]
      _ = C := by rw [← mul_assoc, Ring.inverse_mul_cancel A hu, one_mul]
  have hs : a⁻¹ * (β : ℂ) = ((poleLocation β : ℂ) - z)⁻¹ := by
    rw [haform, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hβc, mul_one]
  refine ⟨hu, ?_⟩
  change B * Ring.inverse A = _
  rw [hi]
  dsimp [C]
  rw [mul_add, mul_smul_comm, hBP, smul_smul, hs]
  rfl

theorem exists_laurent_disk
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (β : ℝ) (hβ : β ≠ 0)
    (hiso : KPIsolatedProjection.IsIsolatedSpectralPoint B β) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z : ℂ, ‖z - (poleLocation β : ℂ)‖ < r →
        IsUnit (correctedPencil B β z)) ∧
      AnalyticOnNhd ℂ (holomorphicComplement B β)
        (Metric.ball (poleLocation β : ℂ) r) ∧
      (∀ z : ℂ, 0 < ‖z - (poleLocation β : ℂ)‖ →
        ‖z - (poleLocation β : ℂ)‖ < r →
        IsUnit (KPResolventPencil.shiftedPencil B z) ∧
        KPResolventPencil.shiftedResolvent B z =
          ((poleLocation β : ℂ) - z)⁻¹ • KPIsolatedProjection.projection B β +
            holomorphicComplement B β z) := by
  have hμ : IsUnit (correctedPencil B β (poleLocation β : ℂ)) := by
    simpa [correctedPencil, KPResolventPencil.shiftedPencil, poleLocation] using
      KPIsolatedProjection.isUnit_gap_add_projection B hB β hβ hiso
  have hopen : IsOpen {z : ℂ | IsUnit (correctedPencil B β z)} := by
    apply Units.isOpen.preimage
    unfold correctedPencil KPResolventPencil.shiftedPencil
    fun_prop
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (poleLocation β : ℂ) hμ
  refine ⟨r, hr, ?_, ?_, ?_⟩
  · intro z hz
    exact hball (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  · intro z hz
    have hT : AnalyticAt ℂ (correctedPencil B β) z := by
      unfold correctedPencil KPResolventPencil.shiftedPencil
      exact (analyticAt_const.sub
        ((analyticAt_id.add analyticAt_const).smul analyticAt_const)).add analyticAt_const
    have hi := analyticOnNhd_inverse (𝕜 := ℂ) _ (hball hz)
    exact (analyticAt_const.mul (hi.comp hT)).mul analyticAt_const
  · intro z hz hzr
    obtain ⟨_, _, hPP, _, hBP, hPB⟩ := KPIsolatedProjection.projection_spec B hB β hβ hiso
    exact pencil_decomposition B β hβ z (sub_ne_zero.mp (norm_pos_iff.mp hz)) hPP hBP hPB
      (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hzr))

theorem simplePole
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (β : ℝ) (hβ : β ≠ 0)
    (hiso : KPIsolatedProjection.IsIsolatedSpectralPoint B β) :
    KPIsolatedProjection.projection B β ≠ 0 ∧
      MeromorphicAt (KPResolventPencil.shiftedResolvent B) (poleLocation β : ℂ) ∧
      meromorphicOrderAt (KPResolventPencil.shiftedResolvent B) (poleLocation β : ℂ) =
        ((-1 : ℤ) : WithTop ℤ) ∧
      Tendsto
        (fun z : ℂ => (z - (poleLocation β : ℂ)) •
          KPResolventPencil.shiftedResolvent B z)
        (𝓝[≠] (poleLocation β : ℂ)) (𝓝 (-KPIsolatedProjection.projection B β)) ∧
      (¬ ∃ G : ℂ → (H →L[ℂ] H),
        ContinuousAt G (poleLocation β : ℂ) ∧
        G =ᶠ[𝓝[≠] (poleLocation β : ℂ)] KPResolventPencil.shiftedResolvent B) ∧
      (FiniteDimensional ℂ (KPIsolatedProjection.eigenspace B β) →
        FiniteDimensional ℂ (KPIsolatedProjection.projection B β).range) := by
  let μ : ℂ := (poleLocation β : ℂ)
  let P := KPIsolatedProjection.projection B β
  let F := holomorphicComplement B β
  let R := KPResolventPencil.shiftedResolvent B
  obtain ⟨hP, _, _, _, _, _⟩ := KPIsolatedProjection.projection_spec B hB β hβ hiso
  obtain ⟨r, hr, _, hF, hR⟩ := exists_laurent_disk B hB β hβ hiso
  have hFan : AnalyticAt ℂ F μ := hF μ (Metric.mem_ball_self hr)
  let g : ℂ → (H →L[ℂ] H) := fun z => -P + (z - μ) • F z
  have hgan : AnalyticAt ℂ g μ :=
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul hFan)
  have hg0 : g μ = -P := by simp [g]
  have hgneq : g μ ≠ 0 := by simpa [hg0] using neg_ne_zero.mpr hP
  have hev : ∀ᶠ z in 𝓝[≠] μ,
      R z = (z - μ) ^ (-1 : ℤ) • g z := by
    have hb : ∀ᶠ z in 𝓝[≠] μ, z ∈ Metric.ball μ r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds μ hr)
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hzne
    have hz0 : z - μ ≠ 0 := sub_ne_zero.mpr (by simpa using hzne)
    have he := (hR z (norm_pos_iff.mpr hz0)
      (by simpa [Metric.mem_ball, dist_eq_norm] using hz)).2
    change R z = (μ - z)⁻¹ • P + F z at he
    rw [he]
    dsimp [g]
    rw [zpow_neg_one, smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    congr 1
    rw [← neg_smul, ← inv_neg, neg_sub]
  have hm : MeromorphicAt R μ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-1, g, hgan, hev⟩
  have ho : meromorphicOrderAt R μ = ((-1 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff hm).mpr ⟨g, hgan, hgneq, hev⟩
  have hscale : (fun z => (z - μ) • R z) =ᶠ[𝓝[≠] μ] g := by
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hzne
    have hz0 : z - μ ≠ 0 := sub_ne_zero.mpr (by simpa using hzne)
    rw [hz, zpow_neg_one, smul_smul, mul_inv_cancel₀ hz0, one_smul]
  have ht : Tendsto (fun z => (z - μ) • R z) (𝓝[≠] μ) (𝓝 (-P)) := by
    rw [← hg0]
    exact hgan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' hscale.symm
  refine ⟨hP, hm, ho, ht, ?_, ?_⟩
  · rintro ⟨G, hG, heq⟩
    have hlim : Tendsto R (𝓝[≠] μ) (𝓝 (G μ)) :=
      (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' heq
    have hnonneg := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hm).mp ⟨G μ, hlim⟩
    rw [ho] at hnonneg
    have hlt : (((-1 : ℤ) : WithTop ℤ)) < 0 := by
      exact_mod_cast (by norm_num : (-1 : ℤ) < 0)
    exact (not_le_of_gt hlt) hnonneg
  · intro hfin
    letI := hfin
    exact KPIsolatedProjection.projection_finiteRank B β

end
end DedekindZetaZeroFree.KPIsolatedLaurent
