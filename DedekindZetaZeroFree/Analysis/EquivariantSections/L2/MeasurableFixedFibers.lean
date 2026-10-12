module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestEnergy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree
namespace KPMeasurableLocalL2

open MeasureTheory Filter
open scoped Topology

variable {X E Γ : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] [Group Γ] [Fintype Γ]

structure Data (X E Γ : Type*) [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [MeasurableSpace E] [BorelSpace E] [Group Γ] [Fintype Γ] where
  measure : Measure X
  action : Γ → X ≃ᵐ X
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ γ δ x, action (γ * δ) x = action γ (action δ x)
  invariant_measure : ∀ γ, MeasurePreserving (action γ) measure measure
  tensor : Γ → X → E ≃ₗᵢ[ℂ] E
  measurable_tensor : ∀ γ, Measurable (fun p : X × E => tensor γ p.1 p.2)
  tensor_one : ∀ x, tensor 1 x = LinearIsometryEquiv.refl ℂ E
  tensor_mul : ∀ γ δ x v,
    tensor (γ * δ) x v = tensor γ (action δ x) (tensor δ x v)

variable (D : Data X E Γ)

structure Piece where
  set : Set X
  measurableSet : MeasurableSet set
  invariant : ∀ γ x, D.action γ x ∈ set ↔ x ∈ set

def SupportedCovariant (S : Piece D) (f : Lp E 2 D.measure) : Prop :=
  (∀ γ : Γ, ∀ᵐ x ∂D.measure, f (D.action γ x) = D.tensor γ x (f x)) ∧
    (∀ᵐ x ∂D.measure, x ∉ S.set → f x = 0)

def Q (S : Piece D) : Submodule ℂ (Lp E 2 D.measure) where
  carrier := {f | SupportedCovariant D S f}
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · intro γ
      filter_upwards [(D.invariant_measure γ).quasiMeasurePreserving.ae
        (Lp.coeFn_zero E 2 D.measure), Lp.coeFn_zero E 2 D.measure] with x h1 h2
      rw [h1, h2, Pi.zero_apply, Pi.zero_apply, map_zero]
    · filter_upwards [Lp.coeFn_zero E 2 D.measure] with x hx _
      exact hx
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_⟩
    · intro γ
      filter_upwards [(D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_add f g), Lp.coeFn_add f g, hf.1 γ, hg.1 γ] with x h1 h2 h3 h4
      simp only [Function.comp_apply] at h1
      simp only [h1, h2, Pi.add_apply, map_add, h3, h4]
    · filter_upwards [Lp.coeFn_add f g, hf.2, hg.2] with x h1 h2 h3 hx
      rw [h1, Pi.add_apply, h2 hx, h3 hx, add_zero]
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · intro γ
      filter_upwards [(D.invariant_measure γ).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_smul c f), Lp.coeFn_smul c f, hf.1 γ] with x h1 h2 h3
      simp only [Function.comp_apply, Pi.smul_apply] at h1 h2
      rw [h1, h2, map_smul, h3]
    · filter_upwards [Lp.coeFn_smul c f, hf.2] with x h1 h2 hx
      rw [h1, Pi.smul_apply, h2 hx, smul_zero]

@[simp] theorem mem_Q_iff (S : Piece D) (f : Lp E 2 D.measure) :
    f ∈ Q D S ↔ SupportedCovariant D S f := Iff.rfl

theorem Q_isClosed (S : Piece D) : IsClosed (Q D S : Set (Lp E 2 D.measure)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u f hu hlim
  have hu' : ∀ n, SupportedCovariant D S (u n) := fun n => (mem_Q_iff D S (u n)).mp (hu n)
  refine (mem_Q_iff D S f).mpr ⟨?_, ?_⟩
  · intro γ
    obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    have hcov : ∀ᵐ x ∂D.measure, ∀ k, u (ns k) (D.action γ x) = D.tensor γ x (u (ns k) x) :=
      ae_all_iff.mpr fun k => (hu' (ns k)).1 γ
    have hconv2 : ∀ᵐ x ∂D.measure,
        Tendsto (fun k => u (ns k) (D.action γ x)) atTop (𝓝 (f (D.action γ x))) :=
      (D.invariant_measure γ).quasiMeasurePreserving.ae hns
    filter_upwards [hns, hcov, hconv2] with x hx hcovx hx2
    have h3 : Tendsto (fun k => D.tensor γ x (u (ns k) x)) atTop
        (𝓝 (D.tensor γ x (f x))) :=
      ((D.tensor γ x).continuous.tendsto (f x)).comp hx
    have h4 : Tendsto (fun k => D.tensor γ x (u (ns k) x)) atTop (𝓝 (f (D.action γ x))) := by
      rw [show (fun k => D.tensor γ x (u (ns k) x)) =
        (fun k => u (ns k) (D.action γ x)) from funext fun k => (hcovx k).symm]
      exact hx2
    exact tendsto_nhds_unique h4 h3
  · obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    have hsup : ∀ᵐ x ∂D.measure, ∀ k, x ∉ S.set → u (ns k) x = 0 :=
      ae_all_iff.mpr fun k => (hu' (ns k)).2
    filter_upwards [hns, hsup] with x hx hsupx
    intro hxs
    have h0 : Tendsto (fun k => u (ns k) x) atTop (𝓝 (0 : E)) := by
      rw [show (fun k => u (ns k) x) = fun _ => (0 : E) from funext fun k => hsupx k hxs]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hx h0

instance Q_innerProductSpace (S : Piece D) : InnerProductSpace ℂ (Q D S) :=
  inferInstanceAs (InnerProductSpace ℂ ↥(Q D S))

instance Q_completeSpace (S : Piece D) : CompleteSpace (Q D S) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  exact (Q_isClosed D S).completeSpace_coe

theorem Q_inner_eq_integral (S : Piece D) (f g : Q D S) :
    inner ℂ f g = ∫ x, inner ℂ ((f : Lp E 2 D.measure) x)
      ((g : Lp E 2 D.measure) x) ∂D.measure := by
  rw [Submodule.coe_inner, L2.inner_def]

theorem Q_integrable_inner (S : Piece D) (f g : Q D S) :
    Integrable (fun x => inner ℂ ((f : Lp E 2 D.measure) x)
      ((g : Lp E 2 D.measure) x)) D.measure :=
  L2.integrable_inner (f : Lp E 2 D.measure) (g : Lp E 2 D.measure)

def fixedFiber (x : X) : Submodule ℂ E where
  carrier := {v | ∀ γ : Γ, D.action γ x = x → D.tensor γ x v = v}
  zero_mem' := by intro γ _; simp
  add_mem' := by
    intro a b ha hb γ hγ
    rw [map_add, ha γ hγ, hb γ hγ]
  smul_mem' := by
    intro c a ha γ hγ
    rw [map_smul, ha γ hγ]

@[simp] theorem mem_fixedFiber_iff (x : X) (v : E) :
    v ∈ fixedFiber D x ↔
      ∀ γ : Γ, D.action γ x = x → D.tensor γ x v = v := Iff.rfl

def supportedAverage (S : Piece D) (h : X → E) : X → E :=
  S.set.indicator (fun x => (Fintype.card Γ : ℂ)⁻¹ •
    ∑ γ : Γ, (D.tensor γ x).symm (h (D.action γ x)))

 def avgField (h : X → E) : X → E :=
  fun y => (Fintype.card Γ : ℂ)⁻¹ •
    ∑ γ : Γ, (D.tensor γ y).symm (h (D.action γ y))

private lemma supportedAverage_eq (S : Piece D) (h : X → E) :
    supportedAverage D S h = S.set.indicator (avgField D h) := rfl

private lemma tensor_mul_symm (δ γ : Γ) (x : X) (w : E) :
    (D.tensor δ (D.action γ x)).symm w =
      D.tensor γ x ((D.tensor (δ * γ) x).symm w) := by
  have h := D.tensor_mul δ γ x ((D.tensor (δ * γ) x).symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [LinearIsometryEquiv.symm_apply_eq]
  exact h

private lemma avgField_covariant (h : X → E) (γ : Γ) (x : X) :
    avgField D h (D.action γ x) = D.tensor γ x (avgField D h x) := by
  rw [show avgField D h = (fun y => (Fintype.card Γ : ℂ)⁻¹ •
      ∑ δ : Γ, (D.tensor δ y).symm (h (D.action δ y))) from rfl]
  dsimp only
  rw [map_smul, map_sum]
  congr 1
  rw [show ∑ δ : Γ, (D.tensor δ (D.action γ x)).symm (h (D.action δ (D.action γ x)))
      = ∑ δ : Γ, D.tensor γ x ((D.tensor (δ * γ) x).symm (h (D.action (δ * γ) x))) from
    Finset.sum_congr rfl fun δ _ => by
      rw [tensor_mul_symm D δ γ x]
      congr 1
      rw [← D.action_mul]]
  exact Equiv.sum_comp (Equiv.mulRight γ)
    (fun δ => D.tensor γ x ((D.tensor δ x).symm (h (D.action δ x))))

private lemma symm_apply_eq_sum (T : E ≃ₗᵢ[ℂ] E) (w : E) :
    T.symm w = ∑ i, inner ℂ (T ((stdOrthonormalBasis ℂ E) i)) w •
      (stdOrthonormalBasis ℂ E) i := by
  conv_lhs => rw [← (stdOrthonormalBasis ℂ E).sum_repr' (T.symm w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← LinearIsometryEquiv.inner_map_map T ((stdOrthonormalBasis ℂ E) i) (T.symm w),
    LinearIsometryEquiv.apply_symm_apply]

theorem supportedAverage_measurable (S : Piece D) (h : X → E)
    (hh : Measurable h) : Measurable (supportedAverage D S h) := by
  haveI : SecondCountableTopology E := by
    let d := Module.finrank ℂ E
    let e₁ : E ≃L[ℂ] Fin d → ℂ :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun (R := ℂ)).symm
    exact e₁.toHomeomorph.secondCountableTopology
  haveI : MeasurableAdd₂ E := inferInstance
  rw [supportedAverage_eq]
  refine Measurable.indicator ?_ S.measurableSet
  change Measurable (fun y => (Fintype.card Γ : ℂ)⁻¹ •
    ∑ δ : Γ, (D.tensor δ y).symm (h (D.action δ y)))
  refine Measurable.const_smul ?_ _
  refine Finset.measurable_sum _ fun δ _ => ?_
  have hsymm : Measurable (fun x => (D.tensor δ x).symm (h (D.action δ x))) := by
    have hfun : (fun x => (D.tensor δ x).symm (h (D.action δ x)))
        = fun x => ∑ i, inner ℂ (D.tensor δ x ((stdOrthonormalBasis ℂ E) i))
            (h (D.action δ x)) • (stdOrthonormalBasis ℂ E) i := by
      funext x
      exact symm_apply_eq_sum (D.tensor δ x) (h (D.action δ x))
    rw [hfun]
    refine Finset.measurable_sum _ fun i _ => ?_
    refine ((continuous_id.smul continuous_const).measurable.comp ?_)
    have hAB : Measurable (fun x =>
        ((D.tensor δ x ((stdOrthonormalBasis ℂ E) i)), h (D.action δ x))) :=
      Measurable.prodMk
        ((D.measurable_tensor δ).comp (measurable_id.prodMk measurable_const))
        (hh.comp (D.action δ).measurable)
    exact (continuous_inner (𝕜 := ℂ) (E := E)).measurable.comp hAB
  exact hsymm

theorem supportedAverage_covariant (S : Piece D) (h : X → E) (γ : Γ) (x : X) :
    supportedAverage D S h (D.action γ x) =
      D.tensor γ x (supportedAverage D S h x) := by
  rw [supportedAverage_eq]
  by_cases hx : x ∈ S.set
  · have hx' : D.action γ x ∈ S.set := (S.invariant γ x).mpr hx
    rw [Set.indicator_of_mem hx' _, Set.indicator_of_mem hx _]
    exact avgField_covariant D h γ x
  · have hx' : D.action γ x ∉ S.set := fun hc => hx ((S.invariant γ x).mp hc)
    rw [Set.indicator_of_notMem hx' _, Set.indicator_of_notMem hx _, map_zero]

theorem supportedAverage_zero_off (S : Piece D) (h : X → E) (x : X)
    (hx : x ∉ S.set) : supportedAverage D S h x = 0 := by
  rw [supportedAverage_eq, Set.indicator_of_notMem hx _]

theorem supportedAverage_ae_eq (S : Piece D) (f : Q D S) (h : X → E)
    (hh : h =ᵐ[D.measure] (f : Lp E 2 D.measure)) :
    supportedAverage D S h =ᵐ[D.measure] (f : Lp E 2 D.measure) := by
  have hcov : ∀ᵐ x ∂D.measure, ∀ δ : Γ,
      h (D.action δ x) = D.tensor δ x ((f : Lp E 2 D.measure) x) := by
    refine ae_all_iff.mpr fun δ => ?_
    filter_upwards [(D.invariant_measure δ).quasiMeasurePreserving.ae hh, (f.2).1 δ] with x h1 h2
    rw [h1, h2]
  filter_upwards [hcov, (f.2).2] with x hcovx hsupx
  rw [supportedAverage_eq]
  by_cases hx : x ∈ S.set
  · rw [Set.indicator_of_mem hx _, avgField]
    have hsum : ∀ δ : Γ, (D.tensor δ x).symm (h (D.action δ x)) =
        (f : Lp E 2 D.measure) x := by
      intro δ
      rw [hcovx δ, LinearIsometryEquiv.symm_apply_apply]
    rw [Finset.sum_congr rfl fun δ _ => hsum δ, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    have hcard : (Fintype.card Γ : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]
  · rw [Set.indicator_of_notMem hx _, hsupx hx]

def borelVersion (f : Lp E 2 D.measure) : X → E :=
  (Lp.aestronglyMeasurable f).mk f

def representative (S : Piece D) (f : Q D S) : X → E :=
  supportedAverage D S (borelVersion D (f : Lp E 2 D.measure))

theorem representative_spec (S : Piece D) (f : Q D S) :
    Measurable (representative D S f) ∧
    (representative D S f =ᵐ[D.measure] (f : Lp E 2 D.measure)) ∧
    (∀ x, x ∉ S.set → representative D S f x = 0) ∧
    (∀ γ x, representative D S f (D.action γ x) =
      D.tensor γ x (representative D S f x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact supportedAverage_measurable D S _
      (Lp.aestronglyMeasurable (f : Lp E 2 D.measure)).stronglyMeasurable_mk.measurable
  · exact supportedAverage_ae_eq D S f _
      (Lp.aestronglyMeasurable (f : Lp E 2 D.measure)).ae_eq_mk.symm
  · intro x hx
    exact supportedAverage_zero_off D S _ x hx
  · intro γ x
    exact supportedAverage_covariant D S _ γ x

theorem representative_memLp (S : Piece D) (f : Q D S) :
    MemLp (representative D S f) 2 D.measure :=
  (Lp.memLp (f : Lp E 2 D.measure)).ae_eq (representative_spec D S f).2.1.symm

end KPMeasurableLocalL2
end DedekindZetaZeroFree

end
