module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexCompactSphericalCharts
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicCharacterProjection

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Matrix.Norms.Elementwise

theorem principalSeries_compact_continuous_fiberInvariant (s : ℝ)
    (f : PrincipalSeries s) :
    Continuous (compactRestriction s f) ∧
      ∀ k t : ComplexSU2, compactSphereCoordinate k = compactSphereCoordinate t →
        f (complexSU2Embedding k) = f (complexSU2Embedding t) := by
  constructor
  · have hf := ((principalSeries_mem_iff s f).mp f.property).2.continuousOn
    have hm : Continuous (fun k : ComplexSU2 =>
        (complexSU2Embedding k : Matrix (Fin 2) (Fin 2) ℂ)) :=
      continuous_subtype_val
    have hc := hf.comp_continuous hm (fun k =>
      Matrix.GeneralLinearGroup.det_ne_zero (complexSU2Embedding k))
    have he : ∀ k : ComplexSU2,
        matrixFunction f (complexSU2Embedding k : Matrix (Fin 2) (Fin 2) ℂ) =
          compactRestriction s f k := by
      intro k
      rw [matrixFunction, dif_pos (Matrix.GeneralLinearGroup.det_ne_zero
        (complexSU2Embedding k))]
      change f _ = f (complexSU2Embedding k)
      congr 1
    simpa only [Function.comp_def, he] using hc
  · intro k t h
    apply ComplexFractionalInverse.compactRestriction_hopf_fiber s f k t
    apply Subtype.ext
    change WithLp.toLp 2 (fun i => (compactSphereCoordinate k i).re) =
      WithLp.toLp 2 (fun i => (compactSphereCoordinate t i).re)
    rw [h]

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues Filter

lemma coord_cont : Continuous compactSphereCoordinate := by
  have h0 : Continuous (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0) :=
    (continuous_apply 0).comp ((continuous_apply 1).comp continuous_subtype_val)
  have h1 : Continuous (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1) :=
    (continuous_apply 1).comp ((continuous_apply 1).comp continuous_subtype_val)
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun k : ComplexSU2 => ((2 * ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
      star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).re : ℝ) : ℂ))
    exact Complex.continuous_ofReal.comp (continuous_const.mul (Complex.continuous_re.comp (h0.mul h1.star)))
  · change Continuous (fun k : ComplexSU2 => ((2 * ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
      star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).im : ℝ) : ℂ))
    exact Complex.continuous_ofReal.comp (continuous_const.mul (Complex.continuous_im.comp (h0.mul h1.star)))
  · change Continuous (fun k : ComplexSU2 => ((‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 -
      ‖(k : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 : ℝ) : ℂ))
    exact Complex.continuous_ofReal.comp ((h0.norm.pow 2).sub (h1.norm.pow 2))

private lemma coord_star (k : ComplexSU2) (i : Fin 3) :
    star (compactSphereCoordinate k i) = compactSphereCoordinate k i := by
  fin_cases i <;> simp [compactSphereCoordinate]

abbrev S := Set.range compactSphereCoordinate

noncomputable def q : C(ComplexSU2, S) :=
  ⟨fun k => ⟨compactSphereCoordinate k, ⟨k, rfl⟩⟩, coord_cont.subtype_mk _⟩

noncomputable def v (i : Fin 3) : C(S, ℂ) :=
  ⟨fun x => x.val i, (continuous_apply i).comp continuous_subtype_val⟩

noncomputable def ev : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] C(S, ℂ) := MvPolynomial.aeval v

private lemma ev_apply (p : MvPolynomial (Fin 3) ℂ) (x : S) :
    ev p x = MvPolynomial.eval x.val p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ev]
  | add p r hp hr => simpa only [map_add, ContinuousMap.add_apply] using congrArg₂ (· + ·) hp hr
  | mul_X p i hp => simpa only [map_mul, ContinuousMap.mul_apply, ev, MvPolynomial.aeval_X, v, ContinuousMap.coe_mk, MvPolynomial.eval_mul, MvPolynomial.eval_X] using congrArg (· * x.val i) hp

lemma star_ev (p : MvPolynomial (Fin 3) ℂ) :
    ∃ r : MvPolynomial (Fin 3) ℂ, ev r = star (ev p) := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C (star a), by ext x; simp [ev]⟩
  | add p r hp hr =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨r', hr'⟩ := hr
    exact ⟨p' + r', by simp [hp', hr']⟩
  | mul_X p i hp =>
    obtain ⟨p', hp'⟩ := hp
    refine ⟨p' * MvPolynomial.X i, ?_⟩
    simp only [map_mul, hp']
    have hv : star (ev (MvPolynomial.X i)) = ev (MvPolynomial.X i) := by
      ext x
      obtain ⟨k, hk⟩ := x.property
      simpa [ev_apply, ← hk] using coord_star k i
    rw [star_mul, hv, mul_comm]

noncomputable def A : StarSubalgebra ℂ C(S, ℂ) where
  toSubalgebra := ev.range
  star_mem' := by
    rintro f ⟨p, rfl⟩
    exact star_ev p

private lemma sep : A.SeparatesPoints := by
  intro x y hxy
  have h : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  refine ⟨ev (MvPolynomial.X i), ?_, ?_⟩
  · exact ⟨ev (MvPolynomial.X i), ⟨MvPolynomial.X i, rfl⟩, rfl⟩
  · simpa [ev_apply] using hi

theorem compact_polynomial_approximation (F : ComplexSU2 → ℂ)
    (hF : Continuous F)
    (hfiber : ∀ k t : ComplexSU2,
      compactSphereCoordinate k = compactSphereCoordinate t → F k = F t) :
    ∃ p : ℕ → MvPolynomial (Fin 3) ℂ,
      TendstoUniformly (fun n => polynomialCompactRestriction (p n)) F atTop := by
  classical
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  letI : CompactSpace S := isCompact_iff_compactSpace.mp
    (isCompact_range coord_cont)
  have hq : Function.Surjective q := by
    rintro ⟨x, k, rfl⟩
    exact ⟨k, rfl⟩
  have hquot : Topology.IsQuotientMap q :=
    Topology.IsQuotientMap.of_surjective_continuous hq q.continuous
  have hfac : Function.FactorsThrough F q := by
    intro k t h
    exact hfiber k t (congrArg Subtype.val h)
  let f : C(S, ℂ) := hquot.lift ⟨F, hF⟩ hfac
  have hdesc : ∀ k, f (q k) = F k := by
    intro k
    exact congrArg (fun g : C(ComplexSU2, ℂ) => g k) (hquot.lift_comp ⟨F, hF⟩ hfac)
  have hmem : f ∈ closure (A : Set C(S, ℂ)) := by
    have ht := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A sep
    change f ∈ (A.topologicalClosure : Set C(S, ℂ))
    rw [ht]
    trivial
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  have hp : ∀ n, ∃ p : MvPolynomial (Fin 3) ℂ, ev p = g n := hg
  choose p hp using hp
  refine ⟨p, ?_⟩
  have hu := (ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim).comp (fun k => q k)
  have hleft : (fun n k => g n (q k)) = (fun n => polynomialCompactRestriction (p n)) := by
    funext n k
    rw [← hp n, ev_apply]
    rfl
  have hright : (fun k => f (q k)) = F := funext hdesc
  simpa only [Function.comp_def, hleft, hright] using hu

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues MeasureTheory Filter
open scoped Topology

private lemma entry_continuous (i j : Fin 2) :
    Continuous (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

private lemma compactSphereCoordinate_continuous :
    Continuous (compactSphereCoordinate : ComplexSU2 → Fin 3 → ℂ) := by
  rw [continuous_pi_iff]
  intro i
  have h : Continuous (fun k : ComplexSU2 =>
      (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) :=
    (entry_continuous 1 0).mul (entry_continuous 1 1).star
  fin_cases i
  · simp only [compactSphereCoordinate, Matrix.cons_val_zero]
    exact RCLike.continuous_ofReal.comp ((Complex.continuous_re.comp h).const_mul 2)
  · simp only [compactSphereCoordinate, Matrix.cons_val_one, Matrix.head_cons]
    exact RCLike.continuous_ofReal.comp ((Complex.continuous_im.comp h).const_mul 2)
  · simp only [compactSphereCoordinate, Matrix.cons_val_two, Matrix.tail_cons]
    exact RCLike.continuous_ofReal.comp
      (((entry_continuous 1 0).norm.pow 2).sub ((entry_continuous 1 1).norm.pow 2))

private lemma polynomialCompactRestriction_continuous (q : MvPolynomial (Fin 3) ℂ) :
    Continuous (polynomialCompactRestriction q) := by
  simp only [polynomialCompactRestriction, LinearMap.coe_mk, AddHom.coe_mk]
  exact (MvPolynomial.continuous_eval q).comp compactSphereCoordinate_continuous

private lemma su2HarmonicCharacter_continuous' (ℓ : ℕ) :
    Continuous (su2HarmonicCharacter ℓ) := by
  have htrace : ∀ n : ℕ, Continuous (fun k : ComplexSU2 =>
      KPCompactHarmonic.symmetricPowerTrace n
        ⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simpa [KPCompactHarmonic.symmetricPowerTrace] using
        (continuous_const : Continuous (fun _ : ComplexSU2 => (1 : ℂ)))
    | one => simp only [KPCompactHarmonic.symmetricPowerTrace]; fun_prop
    | more n hn hn1 =>
        simp only [KPCompactHarmonic.symmetricPowerTrace]
        exact ((by fun_prop : Continuous (fun k : ComplexSU2 =>
            Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn1).sub
          ((by fun_prop : Continuous (fun k : ComplexSU2 =>
            Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn)
  unfold su2HarmonicCharacter KPCompactHarmonic.rankOneCharacter
  simp only [(Matrix.mem_specialUnitaryGroup_iff.mp (Subtype.prop _)).2, one_pow, div_one]
  exact htrace (2 * ℓ)

theorem character_convolution_tendsto_of_uniform (μ : Measure ComplexSU2)
    (hfinite : IsFiniteMeasure μ) (ℓ : ℕ) (F : ComplexSU2 → ℂ)
    (hF : Continuous F) (p : ℕ → MvPolynomial (Fin 3) ℂ)
    (hp : TendstoUniformly (fun n => polynomialCompactRestriction (p n)) F atTop)
    (k : ComplexSU2) :
    Tendsto (fun n => ∫ t : ComplexSU2,
      star (su2HarmonicCharacter ℓ t) *
        polynomialCompactRestriction (p n) (k * t) ∂μ) atTop
      (𝓝 (∫ t : ComplexSU2,
        star (su2HarmonicCharacter ℓ t) * F (k * t) ∂μ)) := by
  classical
  letI : IsFiniteMeasure μ := hfinite
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  have hmul : Continuous (fun t : ComplexSU2 => k * t) := by fun_prop
  have hcomp := hp.comp (fun t : ComplexSU2 => k * t)
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖F x‖ ≤ M := by
    have hbdd : Bornology.IsBounded (Set.range F) := (isCompact_range hF).isBounded
    obtain ⟨M, hM⟩ := hbdd.exists_norm_le
    exact ⟨M, fun x => hM (F x) ⟨x, rfl⟩⟩
  obtain ⟨Mc, hMc⟩ : ∃ M, ∀ x, ‖su2HarmonicCharacter ℓ x‖ ≤ M := by
    have hbdd : Bornology.IsBounded (Set.range fun x : ComplexSU2 =>
        su2HarmonicCharacter ℓ x) :=
      (isCompact_range (su2HarmonicCharacter_continuous' ℓ)).isBounded
    obtain ⟨M, hM⟩ := hbdd.exists_norm_le
    exact ⟨M, fun x => hM (su2HarmonicCharacter ℓ x) ⟨x, rfl⟩⟩
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc (1 : ComplexSU2))
  refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    have hcont : Continuous (fun t : ComplexSU2 =>
        star (su2HarmonicCharacter ℓ t) *
          polynomialCompactRestriction (p n) (k * t)) :=
      ((su2HarmonicCharacter_continuous' ℓ).star).mul
        ((polynomialCompactRestriction_continuous (p n)).comp hmul)
    exact hcont.aestronglyMeasurable
  · refine ⟨Mc * (M + 1), ?_⟩
    filter_upwards [Metric.tendstoUniformly_iff.mp hcomp 1 one_pos] with n hn
    refine Eventually.of_forall fun t => ?_
    have hpoly : ‖polynomialCompactRestriction (p n) (k * t)‖ ≤ M + 1 := by
      have h1 : ‖polynomialCompactRestriction (p n) (k * t) - F (k * t)‖ < 1 := by
        rw [← dist_eq_norm, dist_comm]
        exact hn t
      calc ‖polynomialCompactRestriction (p n) (k * t)‖
          = ‖(polynomialCompactRestriction (p n) (k * t) - F (k * t)) + F (k * t)‖ := by
            ring_nf
        _ ≤ ‖polynomialCompactRestriction (p n) (k * t) - F (k * t)‖ + ‖F (k * t)‖ :=
            norm_add_le _ _
        _ ≤ 1 + M := by linarith [h1.le, hM (k * t)]
        _ = M + 1 := by ring
    rw [norm_mul, norm_star]
    exact mul_le_mul (hMc t) hpoly (norm_nonneg _) hMc0
  · refine Eventually.of_forall fun t => ?_
    exact Filter.Tendsto.const_mul (star (su2HarmonicCharacter ℓ t)) (hcomp.tendsto_at t)

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues

theorem harmonicCompactRestriction_isClosed (ℓ : ℕ) :
    IsClosed (↑((harmonicPolynomials ℓ).map polynomialCompactRestriction) :
      Set (ComplexSU2 → ℂ)) := by
  haveI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ ℓ)
  haveI : FiniteDimensional ℂ (harmonicPolynomials ℓ) :=
    Submodule.finiteDimensional_of_le (show harmonicPolynomials ℓ ≤
      MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ from inf_le_left)
  exact Submodule.closed_of_finiteDimensional _

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open MeasureTheory

theorem characterAverage_compact_polynomial (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ : ℕ) (f : PrincipalSeries s) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p ∈ harmonicPolynomials ℓ ∧
      ∀ k : ComplexSU2,
        polynomialCompactRestriction p k =
          characterAverage s μ ℓ f (complexSU2Embedding k) := by
  classical
  letI : IsProbabilityMeasure μ := hprob
  obtain ⟨hcont, hfiber⟩ :=
    CompactPolynomial.principalSeries_compact_continuous_fiberInvariant s f
  obtain ⟨q, hq⟩ := CompactPolynomial.compact_polynomial_approximation
    (compactRestriction s f) hcont hfiber
  choose p hp hrestriction using
    (fun n => CompactPolynomial.polynomial_character_convolution_realization
      μ hhaar hprob ℓ (q n))
  have hlimit : Filter.Tendsto (fun n => polynomialCompactRestriction (p n))
      Filter.atTop (nhds (fun k => characterAverage s μ ℓ f
        (complexSU2Embedding k))) := by
    apply tendsto_pi_nhds.mpr
    intro k
    have h := CompactPolynomial.character_convolution_tendsto_of_uniform
      μ (inferInstance : IsFiniteMeasure μ) ℓ (compactRestriction s f)
      hcont q hq k
    have hscaled := h.const_mul (((2 * ℓ + 1 : ℕ) : ℂ))
    simpa only [hrestriction, characterAverage_formula, compactRestriction,
      LinearMap.coe_mk, AddHom.coe_mk, map_mul] using hscaled
  have hmem : (fun k => characterAverage s μ ℓ f (complexSU2Embedding k)) ∈
      (harmonicPolynomials ℓ).map polynomialCompactRestriction :=
    (CompactPolynomial.harmonicCompactRestriction_isClosed ℓ).mem_of_tendsto
      hlimit (Filter.Eventually.of_forall (fun n =>
        Submodule.mem_map.mpr ⟨p n, hp n, rfl⟩))
  obtain ⟨r, hr, heq⟩ := Submodule.mem_map.mp hmem
  exact ⟨r, hr, fun k => congrFun heq k⟩

end DedekindZetaZeroFree.KPCplxHarmonicExtraction

end
