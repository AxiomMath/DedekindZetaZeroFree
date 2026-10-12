module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.SiegelCoverAndTruncation

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPFiniteCuspAtlasReduction

private theorem intersection_meanHeight_upper_frame
    (F : Type) [Field F] [NumberField F]
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (Matrix.ProjGenLinGroup.mk A) z) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
        (∑ i : Fin (KPCuspLogShape.dimension F),
          Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
          KPCuspLogShape.dimension F := by
  have h00 : A 0 0 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hA, h]
  have h11 : A 1 1 ≠ 0 := by
    intro h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hA, h]
  rw [KPCuspSiegel.action_mk]
  have hs : ∀ i : Fin (KPCuspLogShape.dimension F),
      (KPCuspSiegel.glAction F A z i).2 = (z i).2 +
        Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖ := by
    intro i
    let ρ := (KPCusp.complexPlace F i).embedding
    apply KPCuspLogShape.upper_action_snd
    · change ρ (A 1 0) = 0
      simp [hA]
    · exact (map_ne_zero ρ).mpr (div_ne_zero h00 h11)
    · change ρ (A 0 0) = ρ (A 0 0 / A 1 1) * ρ (A 1 1)
      rw [← map_mul, div_mul_cancel₀ _ h11]
  simp only [KPCuspLogShape.meanHeight, hs, Finset.sum_add_distrib, add_div]

private theorem intersection_highCusp_upper_frame
    (F : Type) [Field F] [NumberField F]
    (σ : KPCuspArithmetic.PGL2 F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : A 1 0 = 0) (T : ℝ) :
    KPCuspSiegel.highCusp F (σ * Matrix.ProjGenLinGroup.mk A) T =
      KPCuspSiegel.highCusp F σ
        (T + (∑ i : Fin (KPCuspLogShape.dimension F),
          Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
          KPCuspLogShape.dimension F) := by
  let c : ℝ := (∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
      KPCuspLogShape.dimension F
  let u := Matrix.ProjGenLinGroup.mk A
  have hh (z : KPArch.Space (KPCuspLogShape.dimension F)) :
      KPCuspLogShape.meanHeight _ (u • z) = KPCuspLogShape.meanHeight _ z + c :=
    intersection_meanHeight_upper_frame F A hA z
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨u • w, ?_, ?_⟩
    · change T + c < KPCuspLogShape.meanHeight _ (u • w)
      rw [hh]
      simpa only [add_comm] using add_lt_add_right hw c
    · exact (mul_smul σ u w).symm
  · rintro ⟨w, hw, rfl⟩
    refine ⟨u⁻¹ • w, ?_, ?_⟩
    · have he := hh (u⁻¹ • w)
      rw [smul_inv_smul] at he
      change T < KPCuspLogShape.meanHeight _ (u⁻¹ • w)
      change T + c < KPCuspLogShape.meanHeight _ w at hw
      linarith
    · change (σ * u) • (u⁻¹ • w) = σ • w
      rw [mul_smul, smul_inv_smul]

private theorem intersection_highCusp_same_cusp_shift
    (F : Type) [Field F] [NumberField F]
    (σ τ : KPCuspArithmetic.PGL2 F)
    (h : σ • KPCuspArithmetic.infinity F = τ • KPCuspArithmetic.infinity F) :
    ∃ c : ℝ, ∀ T : ℝ,
      KPCuspSiegel.highCusp F τ T = KPCuspSiegel.highCusp F σ (T + c) := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (σ⁻¹ * τ)
  have hf : Matrix.ProjGenLinGroup.mk A • KPCuspArithmetic.infinity F =
      KPCuspArithmetic.infinity F := by
    rw [hA, mul_smul, ← h, inv_smul_smul]
  have hc : A 1 0 = 0 := by
    unfold KPCuspArithmetic.infinity at hf
    rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hf
    obtain ⟨a, ha⟩ := hf
    have hh := congrFun ha 1
    have he : (a • ![1, 0]) 1 = (0 : F) := by simp
    rw [he] at hh
    change 0 = (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) ![1, 0]) 1 at hh
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hh.symm
  refine ⟨(∑ i : Fin (KPCuspLogShape.dimension F),
    Real.log ‖(KPCusp.complexPlace F i).embedding (A 0 0 / A 1 1)‖) /
      KPCuspLogShape.dimension F, fun T => ?_⟩
  have he : τ = σ * Matrix.ProjGenLinGroup.mk A := by rw [hA, mul_inv_cancel_left]
  rw [he]
  exact intersection_highCusp_upper_frame F σ A hc T

theorem commensurable_uniform_high_cusp_intersection
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    {ι : Type*} [Finite ι]
    (q : ι → KPCuspArithmetic.Cusp F)
    (σ : ι → KPCuspArithmetic.PGL2 F)
    (hσ : ∀ a, σ a • KPCuspArithmetic.infinity F = q a)
    (hdistinct : ∀ (a b : ι), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : ι) (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F)),
        z ∈ KPCuspSiegel.highCusp F (σ a) T →
        KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F) z ∈
          KPCuspSiegel.highCusp F (σ b) T →
        a = b ∧ (γ : KPCuspArithmetic.PGL2 F) ∈ KPCuspSiegel.parabolic F Γ (q a) := by
  classical
  let Δ := Γ ⊓ KPCuspArithmetic.projectiveAutomorphisms F M
  have hΔ : ∀ g ∈ Δ, KPCuspArithmetic.PreservesUpToHomothety F M g := by
    intro g hg
    exact (KPCuspArithmetic.preservesUpToHomothety_iff_mem_projectiveAutomorphisms
      F M g).mpr hg.2
  have hΔcomm : Δ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M) :=
    hcomm.inf_left (.refl _)
  obtain ⟨n, Q, frame, t₀, P, B, hn, hframe, hcover, hsep, hPB,
    hboxes, hhigh, hcompact, t₁, ht₁, hends⟩ :=
    kp_cusp_siegel_cover_and_truncation F hF M hM Δ hΔ hΔcomm
  let H := (KPCuspArithmetic.projectiveAutomorphisms F M).subgroupOf Γ
  letI : H.FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hcomm.2
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype (Γ ⧸ H) := Fintype.ofFinite (Γ ⧸ H)
  let r (t : Γ ⧸ H) : KPCuspArithmetic.PGL2 F := (t.out : KPCuspArithmetic.PGL2 F)⁻¹
  let J := ι ⊕ ((Γ ⧸ H) × ι)
  let τ : J → KPCuspArithmetic.PGL2 F := Sum.elim σ (fun p => r p.1 * σ p.2)
  choose j d hd using fun s : J => hcover (τ s • KPCuspArithmetic.infinity F)
  have hframe (s : J) :
      ((d s : KPCuspArithmetic.PGL2 F) * frame (j s)) • KPCuspArithmetic.infinity F =
        τ s • KPCuspArithmetic.infinity F := by
    rw [mul_smul, hframe]
    exact hd s
  choose c hc using fun s : J => intersection_highCusp_same_cusp_shift F
    ((d s : KPCuspArithmetic.PGL2 F) * frame (j s)) (τ s) (hframe s)
  let C : ℝ := ∑ s : J, |c s|
  have hC (s : J) : |c s| ≤ C :=
    Finset.single_le_sum (fun s _ => abs_nonneg (c s)) (Finset.mem_univ s)
  have htransport (s : J) (T : ℝ) (hT : t₁ + C ≤ T)
      (z : KPArch.Space (KPCuspLogShape.dimension F))
      (hz : z ∈ KPCuspSiegel.highCusp F (τ s) T) :
      KPCuspSiegel.action F (d s : KPCuspArithmetic.PGL2 F)⁻¹ z ∈
        KPCuspSiegel.highCusp F (frame (j s)) t₁ := by
    rw [hc s T] at hz
    obtain ⟨w, hw, he⟩ := hz
    refine ⟨w, ?_, ?_⟩
    · change t₁ < KPCuspLogShape.meanHeight _ w
      have hlo := neg_abs_le (c s)
      have hcs := hC s
      change T + c s < KPCuspLogShape.meanHeight _ w at hw
      linarith
    · rw [← he]
      change frame (j s) • w = (d s : KPCuspArithmetic.PGL2 F)⁻¹ •
        (((d s : KPCuspArithmetic.PGL2 F) * frame (j s)) • w)
      rw [mul_smul, inv_smul_smul]
  refine ⟨t₁ + C, ?_⟩
  intro T hT a b γ z hz hγz
  let t : Γ ⧸ H := QuotientGroup.mk γ⁻¹
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H γ⁻¹
  let δ : Δ := ⟨(h : Γ), ⟨(h : Γ).property, h.property⟩⟩
  have hγ : (γ : KPCuspArithmetic.PGL2 F) = (δ : KPCuspArithmetic.PGL2 F) * r t := by
    have he : (t.out : KPCuspArithmetic.PGL2 F) =
        (γ : KPCuspArithmetic.PGL2 F)⁻¹ * (h : Γ) := congrArg Subtype.val hh
    dsimp [r]
    rw [he, mul_inv_rev]
    simp [δ]
  let s : J := Sum.inr (t, a)
  let v : J := Sum.inl b
  let x := KPCuspSiegel.action F (r t) z
  have hx : x ∈ KPCuspSiegel.highCusp F (τ s) T := by
    obtain ⟨w, hw, he⟩ := hz
    refine ⟨w, hw, ?_⟩
    change (r t * σ a) • w = r t • z
    change σ a • w = z at he
    rw [mul_smul, he]
  have hy : (δ : KPCuspArithmetic.PGL2 F) • x ∈
      KPCuspSiegel.highCusp F (τ v) T := by
    change (δ : KPCuspArithmetic.PGL2 F) • (r t • z) ∈
      KPCuspSiegel.highCusp F (σ b) T
    rw [← mul_smul, ← hγ]
    exact hγz
  let η : Δ := (d v)⁻¹ * δ * d s
  let w := KPCuspSiegel.action F (d s : KPCuspArithmetic.PGL2 F)⁻¹ x
  have hw : w ∈ KPCuspSiegel.highCusp F (frame (j s)) t₁ :=
    htransport s T hT x hx
  have hηw : KPCuspSiegel.action F (η : KPCuspArithmetic.PGL2 F) w ∈
      KPCuspSiegel.highCusp F (frame (j v)) t₁ := by
    have hh := htransport v T hT ((δ : KPCuspArithmetic.PGL2 F) • x) hy
    change (η : KPCuspArithmetic.PGL2 F) • w ∈ _
    change (d v : KPCuspArithmetic.PGL2 F)⁻¹ • ((δ : KPCuspArithmetic.PGL2 F) • x) ∈ _ at hh
    simpa [η, w, show KPCuspSiegel.action F = (fun g z => g • z) from rfl, mul_smul] using hh
  have hi := (hends t₁ le_rfl).2.1 (j s) (j v) η w hw hηw
  have hηQ : (η : KPCuspArithmetic.PGL2 F) • Q (j s) = Q (j v) := by
    have hf := (MulAction.mem_stabilizer_iff.mp hi.2.2)
    simpa [hi.1] using hf
  have hγq : (γ : KPCuspArithmetic.PGL2 F) • q a = q b := by
    have he := congrArg (fun u => (d v : KPCuspArithmetic.PGL2 F) • u) hηQ
    have hs := hd s
    have hv := hd v
    change (d s : KPCuspArithmetic.PGL2 F) • Q (j s) =
      (r t * σ a) • KPCuspArithmetic.infinity F at hs
    change (d v : KPCuspArithmetic.PGL2 F) • Q (j v) =
      σ b • KPCuspArithmetic.infinity F at hv
    simp only [η, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul,
      smul_inv_smul] at he
    rw [hs, hv, mul_smul, hσ, hσ, ← mul_smul, ← hγ] at he
    exact he
  have hab : a = b := by
    by_contra hab
    exact hdistinct a b hab γ hγq
  refine ⟨hab, γ.property, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  simpa [hab] using hγq

end DedekindZetaZeroFree.KPFiniteCuspAtlasReduction

end
