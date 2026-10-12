module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicLieGeneration

@[expose] public section

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Topology

private lemma pi_add (s : ℝ) (k : KPCplxCharacterHaar.ComplexPGL2)
    (f g : PrincipalSeries s) : pi s k (f + g) = pi s k f + pi s k g := by
  induction k using Quotient.inductionOn with
  | h k => rfl

private lemma pi_smul (s : ℝ) (k : KPCplxCharacterHaar.ComplexPGL2)
    (c : ℂ) (f : PrincipalSeries s) : pi s k (c • f) = c • pi s k f := by
  induction k using Quotient.inductionOn with
  | h k => rfl

 lemma orbit_span_invariant (s : ℝ) (f : PrincipalSeries s) :
    IsKInvariant s (Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => pi s k f))) := by
  intro k v hv
  let U := Submodule.span ℂ (Set.range (fun k : compactSubgroup => pi s k f))
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [← pi_mul]
      exact Submodule.subset_span ⟨k * h, rfl⟩
  | zero =>
      have hz := pi_smul s k 0 f
      have hz' : pi s k 0 = 0 := by simpa using hz
      rw [hz']
      exact U.zero_mem
  | add x y hx hy ihx ihy =>
      rw [pi_add]
      exact U.add_mem ihx ihy
  | smul c x hx ih =>
      rw [pi_smul]
      exact U.smul_mem c ih

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContHolomorphicKGeneration

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar Matrix
open scoped Classical

def IsKFinite (s : ℝ) (f : PrincipalSeries s) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => pi s k f)))

end DedekindZetaZeroFree.KPContHolomorphicKGeneration

end

end

section

namespace DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped Topology

theorem kFinite_finite_harmonic_decomposition (s : ℝ) (f : PrincipalSeries s)
    (hf : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun k : compactSubgroup => pi s k f)))) :
    ∃ (I : Finset ℕ) (a : ℕ → PrincipalSeries s),
      (∀ ℓ ∈ I, a ℓ ∈ harmonicKType s ℓ) ∧ (∑ ℓ ∈ I, a ℓ) = f := by
  classical
  let U := Submodule.span ℂ (Set.range (fun k : compactSubgroup => pi s k f))
  letI : FiniteDimensional ℂ U := hf
  letI : T2Space (PrincipalSeries s) := principalSeries_t2 s
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  have hclosed : IsClosed (U : Set (PrincipalSeries s)) := U.closed_of_finiteDimensional
  have hinv : IsKInvariant s U := orbit_span_invariant s f
  obtain ⟨μ, hhaar, hprob⟩ := KPCplxHarmonicExtraction.exists_su2_probability_haar
  obtain ⟨a, hint, havg, htype, hlim⟩ :=
    KPCplxHarmonicExtraction.character_average_harmonic_expansion s μ hhaar hprob f
  have haU (ℓ : ℕ) : a ℓ ∈ U := by
    have h := KPCplxHarmonicExtraction.character_average_mem_orbit_closure
      s μ hhaar hprob ℓ f (a ℓ) (hint ℓ) (havg ℓ)
    rwa [hclosed.closure_eq] at h
  have hbound (ℓ : ℕ) (hne : a ℓ ≠ 0) : ℓ < Module.finrank ℂ U := by
    have ht := harmonicKType_multiplicity_one s ℓ
    have hi : IsKInvariant s (U ⊓ harmonicKType s ℓ) := by
      intro k v hv
      exact ⟨hinv k v hv.1, ht.1 k v hv.2⟩
    have hn : U ⊓ harmonicKType s ℓ ≠ ⊥ := by
      intro he
      have hm : a ℓ ∈ U ⊓ harmonicKType s ℓ := ⟨haU ℓ, htype ℓ⟩
      rw [he] at hm
      exact hne (by simpa using hm)
    have he := (ht.2.2.1 (U ⊓ harmonicKType s ℓ) inf_le_right hi).resolve_left hn
    have hle : harmonicKType s ℓ ≤ U := by
      rw [← he]
      exact inf_le_left
    have hd := Submodule.finrank_mono hle
    rw [ht.2.1] at hd
    omega
  have hzero (ℓ : ℕ) (hℓ : Module.finrank ℂ U ≤ ℓ) : a ℓ = 0 := by
    by_contra hn
    have := hbound ℓ hn
    omega
  refine ⟨Finset.range (Module.finrank ℂ U), a, fun ℓ _ => htype ℓ, ?_⟩
  have hsum (N : ℕ) (hN : Module.finrank ℂ U ≤ N) :
      (∑ ℓ ∈ Finset.range N, a ℓ) = ∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ := by
    symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro ℓ hℓ hnot
    exact hzero ℓ (by simpa using hnot)
  have hevent : (fun N => ∑ ℓ ∈ Finset.range N, a ℓ) =ᶠ[Filter.atTop]
      (fun _ : ℕ => ∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ) := by
    filter_upwards [Filter.eventually_ge_atTop (Module.finrank ℂ U)] with N hN
    exact hsum N hN
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hevent.symm) hlim

end DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPContHolomorphicKGeneration

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar Matrix
open scoped Classical

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev RealLieWord := List Mat

noncomputable def rightLieFunction (X : Mat) (f : ComplexGL2 → ℂ)
    (g : ComplexGL2) : ℂ :=
  fderiv ℝ (matrixFunction f) (g : Mat) ((g : Mat) * X)

section
open scoped ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
private theorem lie_inv_open : IsOpen {g : Mat | g.det ≠ 0} := by
  have hc : Continuous (fun g : Mat => g.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  exact isOpen_ne_fun hc continuous_const
private theorem lie_matrix_function_gl (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Mat) = f g := by
  unfold matrixFunction
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  exact Units.ext rfl

theorem rightLieFunction_mem (s : ℝ) (X : Mat) (f : PrincipalSeries s) :
    rightLieFunction X f ∈ principalSeriesSubmodule s := by
  have hF := (principalSeries_mem_iff s f).mp f.property
  let F := matrixFunction (f : ComplexGL2 → ℂ)
  have hdiff (g : ComplexGL2) : DifferentiableAt ℝ F (g : Mat) :=
    (hF.2.contDiffAt (lie_inv_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp)
  apply (principalSeries_mem_iff _ _).mpr
  constructor
  · intro a d b g
    let u := upperTriangular a d b
    let L : Mat →ₗ[ℝ] Mat := {
      toFun := fun h => (u : Mat) * h
      map_add' := fun h k => Matrix.mul_add _ _ _
      map_smul' := fun c h => Matrix.mul_smul _ _ _ }
    let C := L.toContinuousLinearMap
    have hh : (fun h => F (C h)) =ᶠ[nhds (g : Mat)]
        (fun h => (inductionWeight s a d : ℂ) * F h) := by
      filter_upwards [lie_inv_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g)] with h hh
      let q := Matrix.GeneralLinearGroup.mkOfDetNeZero h hh
      change F ((u : Mat) * h) = _
      change F ((u * q : ComplexGL2) : Mat) = _
      dsimp only [F]
      rw [lie_matrix_function_gl]
      change _ = (inductionWeight s a d : ℂ) * matrixFunction _ (q : Mat)
      rw [lie_matrix_function_gl]
      exact hF.1 a d b q
    have hcomp := (hdiff (u * g)).hasFDerivAt.comp (g : Mat) C.hasFDerivAt
    have hmul := (hdiff g).hasFDerivAt.const_mul (inductionWeight s a d : ℂ)
    have he := hh.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (F ∘ C) (g : Mat) = _ at he
    rw [hcomp.fderiv, hmul.fderiv] at he
    have he' := congrArg (fun D : Mat →L[ℝ] ℂ => D ((g : Mat) * X)) he
    simpa [rightLieFunction, F, C, L, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_assoc] using he'
  · have hd := hF.2.fderiv_of_isOpen lie_inv_open (m := ∞) (by simp)
    have hv : ContDiff ℝ ∞ (fun h : Mat => h * X) := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      simp only [Matrix.mul_apply]
      fun_prop
    have hd' := hd.clm_apply hv.contDiffOn
    apply hd'.congr
    intro h hh
    let q := Matrix.GeneralLinearGroup.mkOfDetNeZero h hh
    change matrixFunction (rightLieFunction X f) (q : Mat) = _
    rw [lie_matrix_function_gl]
    rfl

end

noncomputable def rightLieDerivative (s : ℝ) (X : Mat)
    (f : PrincipalSeries s) : PrincipalSeries s :=
  ⟨rightLieFunction X f, rightLieFunction_mem s X f⟩

noncomputable def rightWord (s : ℝ) (w : RealLieWord)
    (f : PrincipalSeries s) : PrincipalSeries s :=
  w.foldr (rightLieDerivative s) f

private lemma rightWord_coe (s : ℝ) (w : RealLieWord) (f : PrincipalSeries s) :
    (rightWord s w f : ComplexGL2 → ℂ) =
      w.foldr (fun X h => rightLieFunction X h) (f : ComplexGL2 → ℂ) := by
  induction w generalizing f with
  | nil => rfl
  | cons X w ih =>
    simp only [rightWord, List.foldr_cons]
    rw [← ih]
    rfl

noncomputable def complexSpherical (z : ℂ) (g : ComplexGL2) : ℂ :=
  let ratio : ℝ :=
    ‖((GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g
  Complex.exp ((1 + 2 * ((positiveParameter : ℂ) + z)) * (Real.log ratio : ℂ))

private lemma bottomRowNormSq_pos (g : ComplexGL2) : 0 < bottomRowNormSq g := by
  unfold bottomRowNormSq
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero g
  by_contra h
  push Not at h
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    have h1 : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ = 0 := by
      nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0),
        norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)]
    simpa using h1
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0 := by
    have h1 : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ = 0 := by
      nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0),
        norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 1)]
    simpa using h1
  exact hdet (by rw [det_fin_two, h10, h11]; ring)

theorem complexSpherical_zero (g : ComplexGL2) :
    complexSpherical 0 g = sphericalSection positiveParameter g := by
  have hratio : 0 < ‖((GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g :=
    div_pos (norm_pos_iff.mpr (Units.ne_zero _)) (bottomRowNormSq_pos g)
  change complexSpherical 0 g = sphericalFunction positiveParameter g
  unfold complexSpherical sphericalFunction
  dsimp only
  change Complex.exp ((1 + 2 * ((positiveParameter : ℂ) + 0)) *
      (Real.log (‖((GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g) : ℂ)) =
    (((‖((GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g) ^
      (1 + 2 * positiveParameter) : ℝ) : ℂ)
  rw [Real.rpow_def_of_pos hratio, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

noncomputable def complexSphericalWord (w : RealLieWord)
    (z : ℂ) (g : ComplexGL2) : ℂ :=
  (w.foldr (fun X f => rightLieFunction X f) (complexSpherical z)) g

theorem complexSphericalWord_zero (w : RealLieWord) (g : ComplexGL2) :
    complexSphericalWord w 0 g =
      rightWord positiveParameter w (sphericalSection positiveParameter) g := by
  have hbase : (complexSpherical 0 : ComplexGL2 → ℂ) =
      (sphericalSection positiveParameter : ComplexGL2 → ℂ) := by
    funext g
    exact complexSpherical_zero g
  rw [complexSphericalWord, rightWord_coe, hbase]

section
open scoped ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
 def invDomain : Set Mat := {h | h.det ≠ 0}
 theorem inv_open : IsOpen invDomain := by
  have hc : Continuous (fun g : Mat => g.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  exact isOpen_ne_fun hc continuous_const
 def phase (h : Mat) : ℂ :=
  (Real.log (‖h.det‖ / (‖h 1 0‖ ^ 2 + ‖h 1 1‖ ^ 2)) : ℂ)
 def exponent (z : ℂ) := 1 + 2 * ((positiveParameter : ℂ) + z)
private theorem exponent_analytic : AnalyticOnNhd ℂ exponent Set.univ := by
  unfold exponent
  exact analyticOnNhd_const.add (analyticOnNhd_const.mul
    (analyticOnNhd_const.add analyticOnNhd_id))
private theorem row_pos (h : Mat) (hh : h ∈ invDomain) :
    0 < ‖h 1 0‖ ^ 2 + ‖h 1 1‖ ^ 2 := by
  by_contra hn
  push Not at hn
  have h10 : h 1 0 = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (h 1 0), norm_nonneg (h 1 1)]
  have h11 : h 1 1 = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (h 1 0), norm_nonneg (h 1 1)]
  exact hh (by rw [det_fin_two, h10, h11]; ring)
 theorem phase_smooth : ContDiffOn ℝ ∞ phase invDomain := by
  have hdet : ContDiff ℝ ∞ (fun h : Mat => h.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  have hnorm := hdet.contDiffOn.norm ℂ (fun h hh => hh)
  have hrow : ContDiff ℝ ∞ (fun h : Mat => ‖h 1 0‖ ^ 2 + ‖h 1 1‖ ^ 2) := by
    apply ContDiff.add
    · exact (by fun_prop : ContDiff ℝ ∞ (fun h : Mat => h 1 0)).norm_sq (𝕜 := ℂ)
    · exact (by fun_prop : ContDiff ℝ ∞ (fun h : Mat => h 1 1)).norm_sq (𝕜 := ℂ)
  have hr := hnorm.div hrow.contDiffOn (fun h hh => ne_of_gt (row_pos h hh))
  have hl := hr.log (fun h hh => ne_of_gt (div_pos (norm_pos_iff.mpr hh) (row_pos h hh)))
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hl

 def atom (a : ℂ → ℂ) (b : Mat → ℂ) (z : ℂ) (h : Mat) : ℂ :=
  Complex.exp (exponent z * phase h) * a z * b h
 inductive Separated : (ℂ → Mat → ℂ) → Prop
  | atom (a : ℂ → ℂ) (b : Mat → ℂ)
      (ha : AnalyticOnNhd ℂ a Set.univ) (hb : ContDiffOn ℝ ∞ b invDomain) :
      Separated (atom a b)
  | add {f g} : Separated f → Separated g → Separated (fun z h => f z h + g z h)
 theorem separated_smooth {H} (hH : Separated H) (z : ℂ) :
    ContDiffOn ℝ ∞ (H z) invDomain := by
  induction hH with
  | atom a b ha hb =>
    exact ((contDiffOn_const.mul phase_smooth).cexp.mul contDiffOn_const).mul hb
  | add hf hg ihf ihg => exact ihf.add ihg
 theorem separated_analytic {H} (hH : Separated H) (h : Mat) :
    AnalyticOnNhd ℂ (fun z => H z h) Set.univ := by
  induction hH with
  | atom a b ha hb =>
    exact ((exponent_analytic.mul analyticOnNhd_const).cexp.mul ha).mul analyticOnNhd_const
  | add hf hg ihf ihg => exact ihf.add ihg
 def direction (X : Mat) (b : Mat → ℂ) (h : Mat) : ℂ :=
  fderiv ℝ b h (h * X)
private theorem direction_smooth (X : Mat) {b} (hb : ContDiffOn ℝ ∞ b invDomain) :
    ContDiffOn ℝ ∞ (direction X b) invDomain := by
  apply (hb.fderiv_of_isOpen inv_open (m := ∞) (by simp)).clm_apply
  have hv : ContDiff ℝ ∞ (fun h : Mat => h * X) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    fun_prop
  exact hv.contDiffOn

 theorem separated_derivative {H} (hH : Separated H) (X : Mat) :
    ∃ H', Separated H' ∧ ∀ z h, h ∈ invDomain →
      H' z h = direction X (H z) h := by
  induction hH with
  | atom a b ha hb =>
    refine ⟨fun z h => atom (fun z => a z * exponent z)
        (fun h => b h * direction X phase h) z h +
        atom a (direction X b) z h,
      Separated.add (Separated.atom _ _ (ha.mul exponent_analytic)
        (hb.mul (direction_smooth X phase_smooth)))
        (Separated.atom _ _ ha (direction_smooth X hb)), ?_⟩
    intro z h hh
    have hp := (phase_smooth.contDiffAt (inv_open.mem_nhds hh)).differentiableAt (by simp)
    have hd := (hb.contDiffAt (inv_open.mem_nhds hh)).differentiableAt (by simp)
    have he := (hp.hasFDerivAt.const_mul (exponent z)).cexp
    have he' := (he.mul_const (a z)).mul hd.hasFDerivAt
    change _ = (fderiv ℝ (((fun y => Complex.exp (exponent z * phase y) * a z) * b)) h) (h * X)
    rw [he'.fderiv]
    simp [atom, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      direction]
    ring
  | @add H G hf hg ihf ihg =>
    obtain ⟨H', hH', eH⟩ := ihf
    obtain ⟨G', hG', eG⟩ := ihg
    refine ⟨fun z h => H' z h + G' z h, hH'.add hG', ?_⟩
    intro z h hh
    dsimp only
    rw [eH z h hh, eG z h hh]
    have hdH := ((separated_smooth hf z).contDiffAt (inv_open.mem_nhds hh)).differentiableAt (by simp)
    have hdG := ((separated_smooth hg z).contDiffAt (inv_open.mem_nhds hh)).differentiableAt (by simp)
    simp only [direction, fderiv_fun_add hdH hdG, ContinuousLinearMap.add_apply]
 theorem matrix_eventually_eq {H : Mat → ℂ} {f : ComplexGL2 → ℂ}
    (he : ∀ g : ComplexGL2, f g = H (g : Mat)) (g : ComplexGL2) :
    matrixFunction f =ᶠ[nhds (g : Mat)] H := by
  filter_upwards [inv_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g)] with h hh
  unfold matrixFunction
  change h.det ≠ 0 at hh
  rw [dif_pos hh]
  exact he (Matrix.GeneralLinearGroup.mkOfDetNeZero h hh)
private theorem word_separated (w : RealLieWord) :
    ∃ H, Separated H ∧ ∀ z g,
      complexSphericalWord w z g = H z (g : Mat) := by
  induction w with
  | nil =>
    refine ⟨atom (fun _ => 1) (fun _ => 1),
      Separated.atom _ _ analyticOnNhd_const contDiffOn_const, ?_⟩
    intro z g
    simp only [complexSphericalWord, List.foldr_nil, complexSpherical, atom,
      exponent, phase, bottomRowNormSq, mul_one]
    rfl
  | cons X w ih =>
    obtain ⟨H, hH, he⟩ := ih
    obtain ⟨H', hH', hd⟩ := separated_derivative hH X
    refine ⟨H', hH', ?_⟩
    intro z g
    change rightLieFunction X (complexSphericalWord w z) g = _
    unfold rightLieFunction
    rw [(matrix_eventually_eq (he z) g).fderiv_eq]
    exact (hd z (g : Mat) (Matrix.GeneralLinearGroup.det_ne_zero g)).symm

theorem complexSphericalWord_holomorphic (w : RealLieWord) (g : ComplexGL2) :
    AnalyticOnNhd ℂ (fun z => complexSphericalWord w z g) Set.univ := by
  obtain ⟨H, hH, he⟩ := word_separated w
  have eq : (fun z => complexSphericalWord w z g) = (fun z => H z (g : Mat)) :=
    funext (fun z => he z g)
  rw [eq]
  exact separated_analytic hH _

end

end DedekindZetaZeroFree.KPContHolomorphicKGeneration

end
end
