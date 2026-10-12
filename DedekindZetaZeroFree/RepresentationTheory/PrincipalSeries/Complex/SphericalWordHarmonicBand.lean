module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPCplxIntertwinerEigenvalues
open ComplexFractionalInverse

theorem polynomialHopf_native_band (p : MvPolynomial (Fin 3) ℂ) :
    ∃ (N : ℕ) (h : PrincipalSeries positiveParameter),
      h ∈ (Finset.range (N + 1)).sup (harmonicKType positiveParameter) ∧
      ∀ k : ComplexSU2, h (complexSU2Embedding k) =
        MvPolynomial.eval (compactSphereCoordinate k) p := by
  classical
  obtain ⟨I, q, hq, he⟩ := finite_fischer_spanning p
  have hlift : ∀ ℓ, ∃ h : PrincipalSeries positiveParameter,
      sphereProfile positiveParameter h = polynomialSphere (q ℓ) := by
    intro ℓ
    exact sphereProfile_surjective positiveParameter _ (polynomialSphere_smooth _)
  choose h hh using hlift
  have hmem : ∀ ℓ ∈ I, h ℓ ∈ harmonicKType positiveParameter ℓ := by
    intro ℓ hℓ
    refine ⟨q ℓ, hq ℓ hℓ, ?_⟩
    funext k
    rw [KPCplxActualImageProof.polynomialCompactRestriction_eq_hopf,
      (sphereProfile_spec positiveParameter (h ℓ)).2 k, hh]
  let N := I.sup id
  refine ⟨N, ∑ ℓ ∈ I, h ℓ, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro ℓ hℓ
    have hℓN : ℓ ≤ N := Finset.le_sup (f := id) hℓ
    exact (Finset.le_sup (s := Finset.range (N + 1))
      (f := harmonicKType positiveParameter) (Finset.mem_range.mpr (Nat.lt_succ_of_le hℓN)))
      (hmem ℓ hℓ)
  · intro k
    have hp := KPCplxActualImageProof.polynomialCompactRestriction_eq_hopf p k
    change MvPolynomial.eval (compactSphereCoordinate k) p = polynomialSphere p (hopf k) at hp
    rw [hp, he]
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    exact ((sphereProfile_spec positiveParameter (h ℓ)).2 k).trans (congrFun (hh ℓ) (hopf k))

open scoped Matrix

def bottomRowMass (g : KPContHolomorphicKGeneration.Mat) : ℂ :=
  g 1 0 * star (g 1 0) + g 1 1 * star (g 1 1)

def bottomRowProjector (g : KPContHolomorphicKGeneration.Mat) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i j => star (g 1 i) * g 1 j / bottomRowMass g

def projectorMassDirection (X P : KPContHolomorphicKGeneration.Mat) : ℂ :=
  Matrix.trace (Xᴴ * P + P * X)

def projectorDirection (X P : KPContHolomorphicKGeneration.Mat) :
    KPContHolomorphicKGeneration.Mat :=
  Xᴴ * P + P * X - projectorMassDirection X P • P

theorem bottomRowMass_eq (g : KPContHolomorphicKGeneration.Mat) :
    bottomRowMass g = ((‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 : ℝ) : ℂ) := by
  simp [bottomRowMass, KPCplxPrincipalSeriesCharts.bottomRowNormSq,
    Complex.star_def, Complex.mul_conj', Complex.ofReal_add]

private theorem mass_ne_zero (g : ComplexGL2) : bottomRowMass g ≠ 0 := by
  rw [bottomRowMass_eq]
  apply Complex.ofReal_ne_zero.mpr
  have hd := Matrix.GeneralLinearGroup.det_ne_zero g
  intro hz
  have h10 : (g : KPContHolomorphicKGeneration.Mat) 1 0 = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg ((g : KPContHolomorphicKGeneration.Mat) 1 0),
      norm_nonneg ((g : KPContHolomorphicKGeneration.Mat) 1 1)]
  have h11 : (g : KPContHolomorphicKGeneration.Mat) 1 1 = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg ((g : KPContHolomorphicKGeneration.Mat) 1 0),
      norm_nonneg ((g : KPContHolomorphicKGeneration.Mat) 1 1)]
  exact hd (by rw [Matrix.det_fin_two, h10, h11]; ring)

private theorem mass_direction_identity (X g : KPContHolomorphicKGeneration.Mat)
    (hg : bottomRowMass g ≠ 0) :
    ((∑ i : Fin 2, ((g * X) 1 i * star (g 1 i) + g 1 i * star ((g * X) 1 i))) /
      bottomRowMass g) = projectorMassDirection X (bottomRowProjector g) := by
  simp only [projectorMassDirection, Matrix.trace, Matrix.diag, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, bottomRowProjector,
    star_add, star_mul]
  field_simp
  <;> ring

theorem bottomRowMass_hasDerivAt
    (X : KPContHolomorphicKGeneration.Mat) (g : ComplexGL2)
    (c : ℝ → KPContHolomorphicKGeneration.Mat)
    (hc : c 0 = g)
    (hd : ∀ i, HasDerivAt (fun t => c t 1 i) (((g : KPContHolomorphicKGeneration.Mat) * X) 1 i) 0) :
    HasDerivAt (fun t => bottomRowMass (c t))
      (bottomRowMass g * projectorMassDirection X (bottomRowProjector g)) 0 := by
  have hraw := ((hd 0).mul (hd 0).star).add ((hd 1).mul (hd 1).star)
  simp only [hc] at hraw
  have he := mass_direction_identity X g (mass_ne_zero g)
  have hn : (∑ i : Fin 2, (((g : KPContHolomorphicKGeneration.Mat) * X) 1 i * star ((g : KPContHolomorphicKGeneration.Mat) 1 i) +
      (g : KPContHolomorphicKGeneration.Mat) 1 i * star (((g : KPContHolomorphicKGeneration.Mat) * X) 1 i))) =
      bottomRowMass g * projectorMassDirection X (bottomRowProjector g) := by
    exact (div_eq_iff (mass_ne_zero g)).mp he |>.trans (mul_comm _ _)
  simp only [Fin.sum_univ_two] at hn
  rw [hn] at hraw
  exact hraw

theorem bottomRowProjector_hasDerivAt
    (X : KPContHolomorphicKGeneration.Mat) (g : ComplexGL2)
    (c : ℝ → KPContHolomorphicKGeneration.Mat)
    (hc : c 0 = g)
    (hd : ∀ i, HasDerivAt (fun t => c t 1 i) (((g : KPContHolomorphicKGeneration.Mat) * X) 1 i) 0)
    (i j : Fin 2) :
    HasDerivAt (fun t => bottomRowProjector (c t) i j)
      (projectorDirection X (bottomRowProjector g) i j) 0 := by
  have hm := bottomRowMass_hasDerivAt X g c hc hd
  have hn := ((hd i).star.mul (hd j)).div hm (by simpa [hc] using mass_ne_zero g)
  simp only [hc] at hn
  change HasDerivAt (fun t => bottomRowProjector (c t) i j) _ 0 at hn
  apply hn.congr_deriv
  dsimp only [Pi.mul_apply]
  rw [hc]
  simp only [projectorDirection, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    bottomRowProjector, star_add, star_mul]
  field_simp
  <;> ring

 def bottomRowOuter (g : KPContHolomorphicKGeneration.Mat) :
    KPContHolomorphicKGeneration.Mat := fun i j => star (g 1 i) * g 1 j
private theorem bottomRowOuter_mul (g k : KPContHolomorphicKGeneration.Mat) :
    bottomRowOuter (g * k) = kᴴ * bottomRowOuter g * k := by
  ext i j
  simp only [bottomRowOuter, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, star_add, star_mul]
  ring
private theorem mass_trace_outer (g : KPContHolomorphicKGeneration.Mat) :
    bottomRowMass g = Matrix.trace (bottomRowOuter g) := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, bottomRowOuter, bottomRowMass]
  ring

theorem bottomRowMass_right_su2 (g : KPContHolomorphicKGeneration.Mat) (k : ComplexSU2) :
    bottomRowMass (g * (k : KPContHolomorphicKGeneration.Mat)) = bottomRowMass g := by
  rw [mass_trace_outer, bottomRowOuter_mul, Matrix.trace_mul_cycle]
  have hk : (k : KPContHolomorphicKGeneration.Mat) * (k : KPContHolomorphicKGeneration.Mat)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1
  rw [hk, Matrix.one_mul, ← mass_trace_outer]

def sphericalRatio (g : ComplexGL2) : ℝ :=
  ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g

theorem sphericalRatio_right_su2 (g : ComplexGL2) (k : ComplexSU2) :
    sphericalRatio (g * complexSU2Embedding k) = sphericalRatio g := by
  have hrow : bottomRowNormSq (g * complexSU2Embedding k) = bottomRowNormSq g := by
    have hm := bottomRowMass_right_su2 (g : KPContHolomorphicKGeneration.Mat) k
    rw [bottomRowMass_eq, bottomRowMass_eq] at hm
    exact Complex.ofReal_injective hm
  unfold sphericalRatio
  rw [hrow, map_mul]
  have hk : ((Matrix.GeneralLinearGroup.det (complexSU2Embedding k) : ℂˣ) : ℂ) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  rw [Units.val_mul, hk, mul_one]

def projectorSpherePolynomial (i j : Fin 2) : MvPolynomial (Fin 3) ℂ :=
  if i = 0 then
    if j = 0 then MvPolynomial.C (1 / 2) * (1 + MvPolynomial.X 2)
    else MvPolynomial.C (1 / 2) * (MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1)
  else
    if j = 0 then MvPolynomial.C (1 / 2) * (MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1)
    else MvPolynomial.C (1 / 2) * (1 - MvPolynomial.X 2)

theorem bottomRowProjector_compact (k : ComplexSU2) (i j : Fin 2) :
    bottomRowProjector k i j =
      MvPolynomial.eval (compactSphereCoordinate k) (projectorSpherePolynomial i j) := by
  have hm : bottomRowMass k = 1 := by
    have hk := RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_compact k
    rw [bottomRowMass_eq]
    exact_mod_cast hk
  have hn : ‖(k : KPContHolomorphicKGeneration.Mat) 1 0‖ ^ 2 +
      ‖(k : KPContHolomorphicKGeneration.Mat) 1 1‖ ^ 2 = 1 :=
    RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_compact k
  have hc := Complex.re_add_im ((k : KPContHolomorphicKGeneration.Mat) 1 0 *
    star ((k : KPContHolomorphicKGeneration.Mat) 1 1))
  fin_cases i <;> fin_cases j <;>
    simp [bottomRowProjector, hm, projectorSpherePolynomial, compactSphereCoordinate,
      Complex.star_def, Complex.mul_conj'] at *
  all_goals apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply] at * <;> nlinarith

theorem projectorPolynomial_native_band
    (p : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    ∃ (N : ℕ) (h : PrincipalSeries positiveParameter),
      h ∈ (Finset.range (N + 1)).sup (harmonicKType positiveParameter) ∧
      ∀ k : ComplexSU2, h (complexSU2Embedding k) =
        MvPolynomial.eval (fun ij => bottomRowProjector k ij.1 ij.2) p := by
  let q := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun ij : Fin 2 × Fin 2 => projectorSpherePolynomial ij.1 ij.2) p
  obtain ⟨N, h, hh, he⟩ := polynomialHopf_native_band q
  refine ⟨N, h, hh, ?_⟩
  intro k
  rw [he]
  dsimp only [q]
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_eval₂]
  have hc : (MvPolynomial.eval (compactSphereCoordinate k)).comp MvPolynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [hc, MvPolynomial.eval₂_id]
  have hi : (fun ij : Fin 2 × Fin 2 => MvPolynomial.eval (compactSphereCoordinate k)
      (projectorSpherePolynomial ij.1 ij.2)) =
      (fun ij => bottomRowProjector k ij.1 ij.2) := by
    funext ij
    exact (bottomRowProjector_compact k ij.1 ij.2).symm
  rw [hi]

theorem determinant_right_hasDerivAt
    (X : KPContHolomorphicKGeneration.Mat) (g : ComplexGL2)
    (c : ℝ → KPContHolomorphicKGeneration.Mat) (hc : c 0 = g)
    (hd : ∀ i j, HasDerivAt (fun t => c t i j)
      (((g : KPContHolomorphicKGeneration.Mat) * X) i j) 0) :
    HasDerivAt (fun t => (c t).det)
      ((g : KPContHolomorphicKGeneration.Mat).det * Matrix.trace X) 0 := by
  have he := ((hd 0 0).mul (hd 1 1)).sub ((hd 0 1).mul (hd 1 0))
  simp only [hc] at he
  simp only [Matrix.det_fin_two]
  apply he.congr_deriv
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.diag,
    Matrix.det_fin_two]
  ring

section NormalizedCalculus
open scoped ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
 abbrev LM := KPContHolomorphicKGeneration.Mat

theorem projectorMassDirection_real (X g : LM) :
    ((projectorMassDirection X (bottomRowProjector g)).re : ℂ) =
      projectorMassDirection X (bottomRowProjector g) := by
  have hm : star (bottomRowMass g) = bottomRowMass g := by
    simp only [bottomRowMass, star_add, star_mul, star_star]
  have hs : star (projectorMassDirection X (bottomRowProjector g)) =
      projectorMassDirection X (bottomRowProjector g) := by
    simp only [projectorMassDirection, Matrix.trace, Matrix.diag, Matrix.add_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, bottomRowProjector]
    simp only [star_add, star_mul, star_div, star_inv₀, star_star, hm]
    simp only [Complex.star_def, map_add, map_mul, map_div₀, map_inv₀, Complex.conj_conj]
    have hm' : star (bottomRowMass g) = bottomRowMass g := hm
    simp only [Complex.star_def] at hm'
    rw [hm']
    ring
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at hi
    simpa using (show 0 = (projectorMassDirection X (bottomRowProjector g)).im by linarith)
private theorem logNormDeriv {f : ℝ → ℂ} {d : ℂ} (hf : HasDerivAt f d 0) (h0 : f 0 ≠ 0) :
    HasDerivAt (fun t => Real.log ‖f t‖) ((d / f 0).re) 0 := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hf.mul hf.star)
  change HasDerivAt (fun t => (f t * star (f t)).re) _ 0 at h
  have he : (fun t => (f t * star (f t)).re) = (fun t => ‖f t‖ ^ 2) := by
    funext t
    simp [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  rw [he] at h
  have hl := (h.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))).div_const 2
  have hl' : (fun t => Real.log (‖f t‖ ^ 2) / 2) = (fun t => Real.log ‖f t‖) := by
    funext t; rw [Real.log_pow]; ring
  rw [hl'] at hl
  apply hl.congr_deriv
  simp only [Complex.reCLM_apply, Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.div_re, Complex.normSq_apply, Complex.sq_norm]
  field_simp
  <;> ring

theorem sphericalLogRatio_hasDerivAt (X : LM) (g : ComplexGL2) (c : ℝ → LM) (hc : c 0 = g)
    (hd : ∀ i j, HasDerivAt (fun t => c t i j) (((g : LM) * X) i j) 0) :
    HasDerivAt (fun t => Real.log (‖(c t).det‖ /
      (‖c t 1 0‖ ^ 2 + ‖c t 1 1‖ ^ 2)))
      ((Matrix.trace X).re - (projectorMassDirection X (bottomRowProjector g)).re) 0 := by
  have hdet := determinant_right_hasDerivAt X g c hc hd
  have hne := Matrix.GeneralLinearGroup.det_ne_zero g
  have hnorm : HasDerivAt (fun t => Real.log ‖(c t).det‖) (Matrix.trace X).re 0 := by
    have h := logNormDeriv hdet (by simpa [hc] using hne)
    simpa [hc, mul_div_cancel_left₀ _ hne] using h
  have hm := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (bottomRowMass_hasDerivAt X g c hc (hd 1))
  change HasDerivAt (fun t => (bottomRowMass (c t)).re) _ 0 at hm
  simp only [bottomRowMass_eq, Complex.reCLM_apply, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hm
  have hrow : 0 < ‖(g : LM) 1 0‖ ^ 2 + ‖(g : LM) 1 1‖ ^ 2 := by
    exact RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_pos g
  have hlog := hm.log (by simpa [hc] using ne_of_gt hrow)
  simp only [hc] at hlog
  have he : (((‖(g : LM) 1 0‖ ^ 2 + ‖(g : LM) 1 1‖ ^ 2) *
      (projectorMassDirection X (bottomRowProjector g)).re) /
      (‖(g : LM) 1 0‖ ^ 2 + ‖(g : LM) 1 1‖ ^ 2)) =
      (projectorMassDirection X (bottomRowProjector g)).re :=
    mul_div_cancel_left₀ _ (ne_of_gt hrow)
  rw [he] at hlog
  apply (hnorm.sub hlog).congr_of_eventuallyEq
  have hct : ContinuousAt (fun t => (c t).det) 0 := hdet.continuousAt
  have hcr : ContinuousAt (fun t => ‖c t 1 0‖ ^ 2 + ‖c t 1 1‖ ^ 2) 0 := hm.continuousAt
  filter_upwards [hct.eventually_ne (by simpa [hc] using hne),
    hcr.eventually_ne (by simpa [hc] using ne_of_gt hrow)] with t ht hr
  exact (Real.log_div (norm_ne_zero_iff.mpr ht) hr)

end NormalizedCalculus

section PolynomialProjectorWords
open scoped Matrix ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

 abbrev BM := KPContHolomorphicKGeneration.Mat
 abbrev PP := MvPolynomial (Fin 2 × Fin 2) ℂ
 def pCoord : Matrix (Fin 2) (Fin 2) PP := fun i j => MvPolynomial.X (i,j)
 def pMass (X : BM) : PP :=
  Matrix.trace ((Xᴴ).map MvPolynomial.C * pCoord + pCoord * X.map MvPolynomial.C)
 def pField (X : BM) : Matrix (Fin 2) (Fin 2) PP :=
  (Xᴴ).map MvPolynomial.C * pCoord + pCoord * X.map MvPolynomial.C - pMass X • pCoord
 def peval (p : PP) (g : BM) : ℂ :=
  MvPolynomial.eval (fun ij => bottomRowProjector g ij.1 ij.2) p
private theorem peval_mass (X g : BM) :
    peval (pMass X) g = projectorMassDirection X (bottomRowProjector g) := by
  simp [peval, pMass, pCoord, projectorMassDirection, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
private theorem peval_field (X g : BM) (i j : Fin 2) :
    peval (pField X i j) g = projectorDirection X (bottomRowProjector g) i j := by
  simp [peval, pField, pMass, pCoord, projectorDirection, projectorMassDirection,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
private theorem p_derivative (X : BM) (p : PP) : ∃ q : PP,
    ∀ (g : ComplexGL2) (c : ℝ → BM), c 0 = g →
      (∀ i, HasDerivAt (fun t => c t 1 i) (((g : BM) * X) 1 i) 0) →
      HasDerivAt (fun t => peval p (c t)) (peval q g) 0 := by
  induction p using MvPolynomial.induction_on with
  | C z => exact ⟨0, by intro g c hc hd; simpa [peval] using hasDerivAt_const (0 : ℝ) z⟩
  | add p r hp hr =>
    obtain ⟨q,hq⟩ := hp
    obtain ⟨u,hu⟩ := hr
    refine ⟨q+u, ?_⟩
    intro g c hc hd
    convert (hq g c hc hd).add (hu g c hc hd) using 1 <;> simp [peval] <;> rfl
  | mul_X p ij hp =>
    obtain ⟨q,hq⟩ := hp
    refine ⟨q * MvPolynomial.X ij + p * pField X ij.1 ij.2, ?_⟩
    intro g c hc hd
    have hf := bottomRowProjector_hasDerivAt X g c hc hd ij.1 ij.2
    have hh := (hq g c hc hd).mul hf
    convert hh using 1 <;> simp [peval, hc, ← peval_field X (g : BM) ij.1 ij.2] <;> rfl
 def bDomain : Set BM := {g | g.det ≠ 0}
private theorem bDomain_open : IsOpen bDomain := by
  have hc : Continuous (fun g : BM => g.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  exact isOpen_ne_fun hc continuous_const
private theorem peval_smooth (p : PP) : ContDiffOn ℝ ∞ (peval p) bDomain := by
  have hcoord : ∀ ij : Fin 2 × Fin 2,
      ContDiffOn ℝ ∞ (fun g : BM => bottomRowProjector g ij.1 ij.2) bDomain := by
    intro ij
    have he (i : Fin 2) : ContDiff ℝ ∞ (fun g : BM => g 1 i) := by fun_prop
    have hm : ContDiff ℝ ∞ bottomRowMass :=
      ((he 0).mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (he 0))).add ((he 1).mul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (he 1)))
    have hn : ContDiff ℝ ∞ (fun g : BM => star (g 1 ij.1) * g 1 ij.2) := by
      convert (((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (he ij.1)).mul (he ij.2)) using 1
      rfl
    have hz : ∀ g ∈ bDomain, bottomRowMass g ≠ 0 := by
      intro g hg
      have hz : bottomRowMass g ≠ 0 := by
        rw [bottomRowMass_eq]
        apply Complex.ofReal_ne_zero.mpr
        have hr := RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_pos
          (Matrix.GeneralLinearGroup.mkOfDetNeZero g hg)
        exact ne_of_gt hr
      exact hz
    convert hn.contDiffOn.mul (hm.contDiffOn.inv hz) using 1
    funext g; simp [bottomRowProjector, div_eq_mul_inv]
  induction p using MvPolynomial.induction_on with
  | C z =>
    convert (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : BM => z) bDomain) using 1
    funext g; simp [peval]
  | add p q hp hq =>
    convert hp.add hq using 1
    funext g; simp [peval]
  | mul_X p ij hp =>
    convert hp.mul (hcoord ij) using 1
    funext g; simp [peval]
 def bDirection (X : BM) (h : BM → ℂ) (g : BM) : ℂ := fderiv ℝ h g (g * X)
private theorem along_right (X : BM) (g : ComplexGL2) (h : BM → ℂ)
    (hh : DifferentiableAt ℝ h (g : BM)) (d : ℂ)
    (hd : HasDerivAt (fun t : ℝ => h ((g : BM) + t • ((g : BM) * X))) d 0) :
    bDirection X h g = d := by
  have hc : HasDerivAt (fun t : ℝ => (g : BM) + t • ((g : BM) * X)) ((g : BM) * X) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((g : BM) * X) |>.const_add (g : BM)
  have he := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
  exact he.unique hd
private theorem p_direction (X : BM) (p : PP) : ∃ q : PP,
    ∀ g : ComplexGL2, bDirection X (peval p) g = peval q g := by
  obtain ⟨q,hq⟩ := p_derivative X p
  refine ⟨q, ?_⟩
  intro g
  apply along_right X g _
    (((peval_smooth p).contDiffAt (bDomain_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp))
  apply hq g _ (by simp)
  intro i
  change HasDerivAt (fun t : ℝ => (g : BM) 1 i + t • (((g : BM) * X) 1 i)) _ 0
  simpa using (hasDerivAt_id (0 : ℝ)).smul_const (((g : BM) * X) 1 i) |>.const_add ((g : BM) 1 i)
 def bPhase (g : BM) : ℂ :=
  (Real.log (‖g.det‖ / (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)) : ℂ)
 def bExponent : Polynomial ℂ :=
  Polynomial.C (1 + 2 * (positiveParameter : ℂ)) + Polynomial.C 2 * Polynomial.X
 def bLog (X : BM) : PP := MvPolynomial.C ((Matrix.trace X).re : ℂ) - pMass X
private theorem bPhase_smooth : ContDiffOn ℝ ∞ bPhase bDomain := by
  have hd : ContDiff ℝ ∞ (fun g : BM => g.det) := by
    simp only [Matrix.det_fin_two]; fun_prop
  have hr : ContDiff ℝ ∞ (fun g : BM => ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) := by
    apply ContDiff.add
    · exact (by fun_prop : ContDiff ℝ ∞ (fun g : BM => g 1 0)).norm_sq (𝕜 := ℂ)
    · exact (by fun_prop : ContDiff ℝ ∞ (fun g : BM => g 1 1)).norm_sq (𝕜 := ℂ)
  have hp : ∀ g ∈ bDomain, 0 < ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 := by
    intro g hg
    exact RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_pos
      (Matrix.GeneralLinearGroup.mkOfDetNeZero g hg)
  have hl := ((hd.contDiffOn.norm ℂ (fun g hg => hg)).div hr.contDiffOn
    (fun g hg => ne_of_gt (hp g hg))).log
    (fun g hg => ne_of_gt (div_pos (norm_pos_iff.mpr hg) (hp g hg)))
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hl
private theorem phase_direction (X : BM) (g : ComplexGL2) :
    bDirection X bPhase g = peval (bLog X) g := by
  apply along_right X g _
    ((bPhase_smooth.contDiffAt (bDomain_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))).differentiableAt (by simp))
  have hc : ∀ i j, HasDerivAt (fun t : ℝ => ((g : BM) + t • ((g : BM) * X)) i j)
      (((g : BM) * X) i j) 0 := by
    intro i j
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (((g : BM) * X) i j) |>.const_add ((g : BM) i j)
  have hl := (sphericalLogRatio_hasDerivAt X g _ (by simp) hc).ofReal_comp
  convert hl using 1
  · rfl
  · change peval (MvPolynomial.C ((Matrix.trace X).re : ℂ) - pMass X) (g : BM) = _
    rw [show peval (MvPolynomial.C ((Matrix.trace X).re : ℂ) - pMass X) (g : BM) =
      ((Matrix.trace X).re : ℂ) - peval (pMass X) (g : BM) by simp [peval]]
    rw [peval_mass, Complex.ofReal_sub, projectorMassDirection_real]

 def bAtom (p : Polynomial ℂ) (q : PP) (s : ℂ) (g : BM) : ℂ :=
  Complex.exp (bExponent.eval s * bPhase g) * p.eval s * peval q g
 inductive ProjectorSeparated : (ℂ → BM → ℂ) → Prop
  | atom (p : Polynomial ℂ) (q : PP) : ProjectorSeparated (bAtom p q)
  | add {H G} : ProjectorSeparated H → ProjectorSeparated G →
      ProjectorSeparated (fun s g => H s g + G s g)
private theorem projectorSeparated_smooth {H} (hH : ProjectorSeparated H) (s : ℂ) :
    ContDiffOn ℝ ∞ (H s) bDomain := by
  induction hH with
  | atom p q => exact ((contDiffOn_const.mul bPhase_smooth).cexp.mul contDiffOn_const).mul (peval_smooth q)
  | add hH hG ihH ihG => exact ihH.add ihG
private theorem projectorSeparated_derivative {H} (hH : ProjectorSeparated H) (X : BM) :
    ∃ H', ProjectorSeparated H' ∧ ∀ s (a : ComplexGL2), H' s (a : BM) = bDirection X (H s) a := by
  induction hH with
  | atom p q =>
    obtain ⟨u,hu⟩ := p_direction X q
    refine ⟨fun s g => bAtom (p * bExponent) (q * bLog X) s g + bAtom p u s g,
      ProjectorSeparated.add (ProjectorSeparated.atom _ _) (ProjectorSeparated.atom _ _), ?_⟩
    intro s a
    have ha := Matrix.GeneralLinearGroup.det_ne_zero a
    have hp := (bPhase_smooth.contDiffAt (bDomain_open.mem_nhds ha)).differentiableAt (by simp)
    have hq := ((peval_smooth q).contDiffAt (bDomain_open.mem_nhds ha)).differentiableAt (by simp)
    have he := (((hp.hasFDerivAt.const_mul (bExponent.eval s)).cexp).mul_const (p.eval s)).mul hq.hasFDerivAt
    change _ = fderiv ℝ ((fun g => Complex.exp (bExponent.eval s * bPhase g) * p.eval s) * peval q) (a : BM) ((a : BM) * X)
    rw [he.fderiv]
    have hphase : fderiv ℝ bPhase (a : BM) ((a : BM) * X) = peval (bLog X) a := phase_direction X a
    have hpoly : fderiv ℝ (peval q) (a : BM) ((a : BM) * X) = peval u a := hu a
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, smul_eq_mul,
      hphase, hpoly, bAtom, Polynomial.eval_mul, peval, map_mul]
    ring
  | @add H G hH hG ihH ihG =>
    obtain ⟨H',hH',eH⟩ := ihH
    obtain ⟨G',hG',eG⟩ := ihG
    refine ⟨fun s g => H' s g + G' s g, ProjectorSeparated.add hH' hG', ?_⟩
    intro s a
    change H' s (a : BM) + G' s (a : BM) = _
    rw [eH s a, eG s a]
    have hdH := ((projectorSeparated_smooth hH s).contDiffAt
      (bDomain_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero a))).differentiableAt (by simp)
    have hdG := ((projectorSeparated_smooth hG s).contDiffAt
      (bDomain_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero a))).differentiableAt (by simp)
    simp only [bDirection, fderiv_fun_add hdH hdG, ContinuousLinearMap.add_apply]
private theorem projectorSeparated_finite {H} (hH : ProjectorSeparated H) :
    ∃ (n : ℕ) (p : Fin n → Polynomial ℂ) (q : Fin n → PP), ∀ s g,
      H s g = Complex.exp (bExponent.eval s * bPhase g) * ∑ j, (p j).eval s * peval (q j) g := by
  induction hH with
  | atom p q =>
    refine ⟨1, fun _ => p, fun _ => q, ?_⟩
    intro s g
    simp [Fin.sum_univ_one, bAtom, mul_assoc]
  | @add H G hH hG ihH ihG =>
    obtain ⟨n,p,q,he⟩ := ihH
    obtain ⟨m,r,u,ge⟩ := ihG
    refine ⟨n+m,Fin.append p r,Fin.append q u,?_⟩
    intro s g
    change H s g + G s g = _
    rw [he,ge,Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,mul_add]
private theorem sphericalWord_projector_separated (w : KPContHolomorphicKGeneration.RealLieWord) :
    ∃ H, ProjectorSeparated H ∧ ∀ s a,
      KPContHolomorphicKGeneration.complexSphericalWord w s a = H s (a : BM) := by
  induction w with
  | nil =>
    refine ⟨bAtom 1 1, ProjectorSeparated.atom _ _, ?_⟩
    intro s a
    simp only [KPContHolomorphicKGeneration.complexSphericalWord, List.foldr_nil,
      KPContHolomorphicKGeneration.complexSpherical, bAtom, bExponent,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_one, mul_one, bPhase, bottomRowNormSq, peval, map_one]
    congr 1
    congr 1
    ring
  | cons X w ih =>
    obtain ⟨H,hH,he⟩ := ih
    obtain ⟨H',hH',hd⟩ := projectorSeparated_derivative hH X
    refine ⟨H',hH',?_⟩
    intro s a
    have heq : matrixFunction (KPContHolomorphicKGeneration.complexSphericalWord w s) =ᶠ[nhds (a : BM)] H s := by
      filter_upwards [bDomain_open.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero a)] with g hg
      unfold matrixFunction
      change g.det ≠ 0 at hg
      rw [dif_pos hg]
      exact he s (Matrix.GeneralLinearGroup.mkOfDetNeZero g hg)
    change fderiv ℝ (matrixFunction (KPContHolomorphicKGeneration.complexSphericalWord w s))
      (a : BM) ((a : BM) * X) = _
    rw [heq.fderiv_eq]
    exact (hd s a).symm

theorem sphericalWord_polynomial_projector_factors
    (w : KPContHolomorphicKGeneration.RealLieWord) :
    ∃ (n : ℕ) (p : Fin n → Polynomial ℂ) (q : Fin n → PP),
      ∀ (s : ℂ) (g : ComplexGL2),
      KPContHolomorphicKGeneration.complexSphericalWord w s g =
        KPContHolomorphicKGeneration.complexSpherical s g *
          ∑ j, (p j).eval s * MvPolynomial.eval
            (fun ij => bottomRowProjector g ij.1 ij.2) (q j) := by
  obtain ⟨H,hH,he⟩ := sphericalWord_projector_separated w
  obtain ⟨n,p,q,hrep⟩ := projectorSeparated_finite hH
  refine ⟨n,p,q,?_⟩
  intro s g
  rw [he,hrep]
  have hexp : Complex.exp (bExponent.eval s * bPhase g) = KPContHolomorphicKGeneration.complexSpherical s g := by
    simp only [bExponent, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, bPhase, KPContHolomorphicKGeneration.complexSpherical, bottomRowNormSq]
    congr 1
    congr 1
    ring
  rw [hexp]
  rfl
end PolynomialProjectorWords

theorem sphericalWord_polynomial_harmonic_band :
    ∀ w : KPContHolomorphicKGeneration.RealLieWord,
      ∃ (N n : ℕ)
        (h : Fin n → KPCplxPrincipalSeriesCharts.PrincipalSeries
          KPCplxPrincipalSeriesCharts.positiveParameter)
        (a : Fin n → Polynomial ℂ),
        (∀ j, h j ∈ (Finset.range (N + 1)).sup
          (KPCplxIntertwinerEigenvalues.harmonicKType
            KPCplxPrincipalSeriesCharts.positiveParameter)) ∧
        ∀ (s : ℂ) (k : KPCplxCharacterHaar.ComplexSU2),
          KPContHolomorphicKGeneration.complexSphericalWord w s
            (KPCplxCharacterHaar.complexSU2Embedding k) =
          ∑ j, (a j).eval s * h j (KPCplxCharacterHaar.complexSU2Embedding k) := by
  intro w
  classical
  obtain ⟨n,p,q,he⟩ := sphericalWord_polynomial_projector_factors w
  choose N h hh eh using (fun j => projectorPolynomial_native_band (q j))
  let M := Finset.univ.sup N
  refine ⟨M,n,h,p,?_,?_⟩
  · intro j
    apply (Finset.sup_mono (f := KPCplxIntertwinerEigenvalues.harmonicKType positiveParameter)
      (Finset.range_mono (Nat.add_le_add_right (Finset.le_sup (f := N) (Finset.mem_univ j)) 1)))
    exact hh j
  · intro s k
    rw [he]
    have hb := RepresentationTheory.KPContHolomorphicKGenerationProve.RaisingCalculation.rowB_compact k
    have hd : (k : BM).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
    have hs : KPContHolomorphicKGeneration.complexSpherical s (complexSU2Embedding k) = 1 := by
      simp only [KPContHolomorphicKGeneration.complexSpherical]
      change Complex.exp ((1 + 2 * ((positiveParameter : ℂ) + s)) *
        (Real.log (‖(k : BM).det‖ / (‖(k : BM) 1 0‖ ^ 2 + ‖(k : BM) 1 1‖ ^ 2)) : ℂ)) = 1
      change ‖(k : BM) 1 0‖ ^ 2 + ‖(k : BM) 1 1‖ ^ 2 = 1 at hb
      rw [hd,hb]
      simp
    rw [hs,one_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [eh j]
    rfl

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

end
