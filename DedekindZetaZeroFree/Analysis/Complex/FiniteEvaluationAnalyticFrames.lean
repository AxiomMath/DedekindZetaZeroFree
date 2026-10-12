module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteHarmonicSampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Classical Topology
namespace DedekindZetaZeroFree.SheetRescaling
open Filter
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming finite_interpolation → finite_interpolation

private theorem frame_det_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) {Ω : Set ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun s => A s i j) Ω) :
    AnalyticOnNhd ℂ (fun s => (A s).det) Ω := by
  intro s hs
  simp_rw [Matrix.det_apply]
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.const_smul
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hA (σ i) i s hs

private theorem frame_inv_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) (hA : ∀ i j, AnalyticAt ℂ (fun s => A s i j) 0)
    (hzero : A 0 = 1) : ∀ i j, AnalyticAt ℂ (fun s => (A s)⁻¹ i j) 0 := by
  have hd : AnalyticAt ℂ (fun s => (A s).det) 0 := by
    simp_rw [Matrix.det_apply]
    apply Finset.analyticAt_fun_sum
    intro σ _
    apply AnalyticAt.const_smul
    apply Finset.analyticAt_fun_prod
    intro i _
    exact hA (σ i) i
  have hn : (A 0).det ≠ 0 := by rw [hzero, Matrix.det_one]; exact one_ne_zero
  intro i j
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply (hd.inv hn).mul
  simp_rw [Matrix.det_apply]
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.const_smul
  apply Finset.analyticAt_fun_prod
  intro k _
  by_cases hk : σ k = j
  · simp only [Matrix.updateRow_self, hk]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne hk]
    exact hA (σ k) k

private theorem frame_inv_meromorphic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) {Ω : Set ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun s => A s i j) Ω) :
    ∀ i j, MeromorphicOn (fun s => (A s)⁻¹ i j) Ω := by
  intro i j
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply (frame_det_analytic A hA).meromorphicOn.inv.mul
  apply AnalyticOnNhd.meromorphicOn
  apply frame_det_analytic
  intro k l s hs
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne hk]
    exact hA k l s hs

theorem analytic_function_frame
    {V Y : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (J : ℂ → V →ₗ[ℂ] (Y → ℂ)) (hJ : Function.Injective (J 0))
    {Ω : Set ℂ} (h0 : (0 : ℂ) ∈ Ω) (hΩ : IsPreconnected Ω)
    (ha : ∀ v y, AnalyticOnNhd ℂ (fun s => J s v y) Ω) :
    ∃ (n : ℕ) (p : Fin n → Y) (b : Fin n → ℂ → V),
      (∀ i, ∀ l : V →ₗ[ℂ] ℂ, AnalyticAt ℂ (fun s => l (b i s)) 0) ∧
      (∀ i, ∀ l : V →ₗ[ℂ] ℂ, MeromorphicOn (fun s => l (b i s)) Ω) ∧
      (∀ᶠ s in 𝓝 (0 : ℂ), ∀ v,
        v = ∑ i, J s v (p i) • b i s) ∧
      (∀ z ∈ Ω, ∀ᶠ s in 𝓝[≠] z, s ∈ Ω → ∀ v,
        v = ∑ i, J s v (p i) • b i s) := by
  let T := (J 0).range
  letI : FiniteDimensional ℂ T := Module.Finite.range (J 0)
  obtain ⟨n,p,u,hu⟩ := finite_interpolation T
  choose b hb using fun i => (u i).property
  have hre : ∀ v : V, v = ∑ i, J 0 v (p i) • b i := by
    intro v
    apply hJ
    ext y
    have he := hu (⟨J 0 v, LinearMap.mem_range.mpr ⟨v,rfl⟩⟩ : T) y
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      hb] using he
  let B := Module.finBasis ℂ V
  let A : ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun s k j => ∑ i, J s (B j) (p i) * B.repr (b i) k
  have hA : ∀ k j, AnalyticOnNhd ℂ (fun s => A s k j) Ω := by
    intro k j s hs
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (ha (B j) (p i) s hs).mul analyticAt_const
  have hAz : A 0 = 1 := by
    ext k j
    have he := congrArg (fun v => B.repr v k) (hre (B j))
    simpa only [A, map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B.repr_self, Finsupp.single_apply,
      Matrix.one_apply, eq_comm] using he.symm
  let c := fun i s => B.repr.symm
    (Finsupp.equivFunOnFinite.symm ((A s)⁻¹.mulVec (fun k => B.repr (b i) k)))
  have hca (i) (l : V →ₗ[ℂ] ℂ) : AnalyticAt ℂ (fun s => l (c i s)) 0 := by
    have he : (fun s => l (c i s)) = fun s =>
        ∑ k, (∑ j, (A s)⁻¹ k j * B.repr (b i) j) * l (B k) := by
      funext s
      have hh := congrArg l (B.sum_repr (c i s))
      simpa only [map_sum, map_smul, smul_eq_mul, c, LinearEquiv.apply_symm_apply,
        Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_finsetSum,
        Finsupp.coe_smul, Matrix.mulVec, dotProduct] using hh.symm
    rw [he]
    apply Finset.analyticAt_fun_sum
    intro k _
    apply AnalyticAt.mul _ analyticAt_const
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (frame_inv_analytic A (fun k j => hA k j 0 h0) hAz k j).mul analyticAt_const
  have hcm (i) (l : V →ₗ[ℂ] ℂ) : MeromorphicOn (fun s => l (c i s)) Ω := by
    have he : (fun s => l (c i s)) = fun s =>
        ∑ k, (∑ j, (A s)⁻¹ k j * B.repr (b i) j) * l (B k) := by
      funext s
      have hh := congrArg l (B.sum_repr (c i s))
      simpa only [map_sum, map_smul, smul_eq_mul, c, LinearEquiv.apply_symm_apply,
        Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_finsetSum,
        Finsupp.coe_smul, Matrix.mulVec, dotProduct] using hh.symm
    rw [he]
    apply MeromorphicOn.fun_sum
    intro k _
    apply MeromorphicOn.mul _ analyticOnNhd_const.meromorphicOn
    apply MeromorphicOn.fun_sum
    intro j _
    exact (frame_inv_meromorphic A hA k j).mul analyticOnNhd_const.meromorphicOn
  have hn : ∀ᶠ s in 𝓝 (0 : ℂ), IsUnit (A s).det := by
    have he := (frame_det_analytic A hA 0 h0).continuousAt.eventually_ne
      (by rw [hAz, Matrix.det_one]; exact one_ne_zero)
    filter_upwards [he] with s hs
    exact isUnit_iff_ne_zero.mpr hs
  have hrec (s : ℂ) (hs : IsUnit (A s).det) (v : V) :
      v = ∑ i, J s v (p i) • c i s := by
    apply B.repr.injective
    apply Finsupp.ext
    intro k
    have hAv : (A s).mulVec (fun j => B.repr v j) =
        fun j => ∑ i, J s v (p i) * B.repr (b i) j := by
      funext j
      simp only [Matrix.mulVec, dotProduct, A, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have he := congrArg (fun v => J s v (p i)) (B.sum_repr v)
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
      rw [← he, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hInv : (A s)⁻¹.mulVec ((A s).mulVec (fun j => B.repr v j)) =
        (fun j => B.repr v j) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hs, Matrix.one_mulVec]
    have hv := congrFun hInv k
    rw [hAv] at hv
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, LinearEquiv.apply_symm_apply,
      Finsupp.equivFunOnFinite_symm_apply_apply, Matrix.mulVec, dotProduct] at hv ⊢
    rw [← hv]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨n,p,c,hca,hcm,?_,?_⟩
  · filter_upwards [hn] with s hs
    exact hrec s hs
  · have hne : ∀ᶠ s in codiscreteWithin Ω, (A s).det ≠ 0 := by
      rcases (frame_det_analytic A hA).eqOn_zero_or_eventually_ne_zero_of_preconnected hΩ with hz | hn
      · have hz0 := hz h0
        simp only [hAz, Matrix.det_one, Pi.zero_apply] at hz0
        exact (one_ne_zero hz0).elim
      · exact hn
    intro z hz
    have he := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hne z hz
    filter_upwards [he] with s hs
    intro hsΩ v
    exact hrec s (isUnit_iff_ne_zero.mpr (hs hsΩ)) v

end DedekindZetaZeroFree.SheetRescaling

end
