module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SU2CharacterBounds

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped Matrix

noncomputable def compactBasis : Fin 1 → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ j => Complex.I • ((1 / (Real.sqrt 2 : ℂ)) •
    (![!![1, 0; 0, -1], !![0, 1; 1, 0], !![0, Complex.I; -Complex.I, 0]] j))

theorem compactBasis_skew (i : Fin 1) (j : Fin 3) :
    star (compactBasis i j) = -compactBasis i j := by
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [compactBasis, Matrix.star_apply, Matrix.conjTranspose_apply]

noncomputable def compactCharacterSecondDerivative (ℓ : ℕ) (j : Fin 3)
    (k : ComplexSU2) : ℂ :=
  RepresentationTheory.KPCompactHarmonicTruncation.Casimir.rankOneSecondDerivative
    compactBasis compactBasis_skew ℓ (0, j)
    ⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
      (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩

open scoped Matrix.Norms.Elementwise in

noncomputable def compactRawDerivative (j : Fin 3) (f : ComplexGL2 → ℂ)
    (g : ComplexGL2) : ℂ :=
  fderiv ℝ (matrixFunction f) (g : Matrix (Fin 2) (Fin 2) ℂ)
    ((g : Matrix (Fin 2) (Fin 2) ℂ) * compactBasis 0 j)

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped Matrix.Norms.Elementwise

private theorem su2HarmonicCharacter_continuous_aux (ℓ : ℕ) :
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

private theorem orbit_continuous (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2) :
    Continuous (fun k : ComplexSU2 => f (g * complexSU2Embedding k)) := by
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (matrixFunction (f : ComplexGL2 → ℂ))
      {A : Matrix (Fin 2) (Fin 2) ℂ | A.det ≠ 0} :=
    ((principalSeries_mem_iff s (f : ComplexGL2 → ℂ)).mp f.property).2
  have hφ : Continuous (fun k : ComplexSU2 =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_const.mul continuous_subtype_val
  have hmaps : ∀ k : ComplexSU2,
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
    intro k
    rw [Matrix.det_mul, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2, mul_one]
    exact Matrix.GeneralLinearGroup.det_ne_zero g
  refine (hfd.continuousOn.comp_continuous hφ hmaps).congr (fun k => ?_)
  simp only [Function.comp_apply]
  have hd : ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
    hmaps k
  rw [matrixFunction, dif_pos hd]
  have harg : Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ)) hd =
      g * complexSU2Embedding k := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [harg]

private theorem characterAverage_integrable_finite (s : ℝ) (μ : Measure ComplexSU2)
    [IsFiniteMeasure μ] (ℓ : ℕ) (f : PrincipalSeries s) (g : ComplexGL2) :
    Integrable (fun k : ComplexSU2 =>
      star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) μ := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  exact (((su2HarmonicCharacter_continuous_aux ℓ).star.mul
    (orbit_continuous s f g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

theorem characterAverage_linear_exists (s : ℝ) (μ : Measure ComplexSU2)
    [IsFiniteMeasure μ] (ℓ : ℕ) (g : ComplexGL2) :
    ∃ A : PrincipalSeries s →ₗ[ℂ] ℂ,
      ∀ f : PrincipalSeries s, A f = characterAverage s μ ℓ f g := by
  have hInt := fun f : PrincipalSeries s => characterAverage_integrable_finite s μ ℓ f g
  have hpt_add : ∀ f₁ f₂ : PrincipalSeries s,
      (fun k : ComplexSU2 =>
        star (su2HarmonicCharacter ℓ k) * (f₁ + f₂) (g * complexSU2Embedding k)) =
      fun k : ComplexSU2 => star (su2HarmonicCharacter ℓ k) * f₁ (g * complexSU2Embedding k) +
        star (su2HarmonicCharacter ℓ k) * f₂ (g * complexSU2Embedding k) := by
    intro f₁ f₂
    funext k
    have hco : (f₁ + f₂) (g * complexSU2Embedding k) =
        f₁ (g * complexSU2Embedding k) + f₂ (g * complexSU2Embedding k) := rfl
    rw [hco, mul_add]
  have hpt_smul : ∀ (c : ℂ) (f : PrincipalSeries s),
      (fun k : ComplexSU2 =>
        star (su2HarmonicCharacter ℓ k) * (c • f) (g * complexSU2Embedding k)) =
      fun k : ComplexSU2 => c * (star (su2HarmonicCharacter ℓ k) *
        f (g * complexSU2Embedding k)) := by
    intro c f
    funext k
    have hco : (c • f) (g * complexSU2Embedding k) = c * f (g * complexSU2Embedding k) := rfl
    rw [hco, mul_left_comm]
  refine ⟨{ toFun := fun f => characterAverage s μ ℓ f g
            map_add' := fun f₁ f₂ => ?_
            map_smul' := fun c f => ?_ }, fun f => rfl⟩
  · rw [characterAverage_formula, characterAverage_formula, characterAverage_formula,
      hpt_add f₁ f₂, integral_add (hInt f₁) (hInt f₂)]
    ring
  · rw [characterAverage_formula, characterAverage_formula, hpt_smul c f, integral_const_mul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open RepresentationTheory.KPCompactHarmonicTruncation.Casimir
open scoped Matrix.Norms.L2Operator Topology
theorem basis_trace (i : Fin 1) (j : Fin 3) : (compactBasis i j).trace = 0 := by
  fin_cases j <;> simp [compactBasis, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
noncomputable def compactCurve (j : Fin 3) (t : ℝ) : ComplexSU2 :=
  ⟨(basisExp compactBasis compactBasis_skew (0,j) t).val,
    Matrix.mem_specialUnitaryGroup_iff.mpr ⟨(basisExp compactBasis compactBasis_skew (0,j) t).property,
      basisExp_det_eq_one compactBasis compactBasis_skew basis_trace (0,j) t⟩⟩
private theorem cheb_smooth (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (chebR n) ∧ ContDiff ℝ (⊤ : ℕ∞) (chebR' n) := by
  induction n with
  | zero => exact ⟨contDiff_const, contDiff_const⟩
  | succ n ih =>
    simp only [chebR_succ, chebR'_succ]
    exact ⟨(contDiff_id.mul ih.2).sub ih.1, ((contDiff_id.mul ih.2).sub ih.1).sub ih.2⟩
private theorem raw_sym (n : ℕ) (u : RepresentationTheory.KPCompactHarmonicTruncation.RawU2) :
    RepresentationTheory.KPCompactHarmonicTruncation.rawSymmetricPowerTrace n u =
      KPCompactHarmonic.symmetricPowerTrace n u := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h h' => simp only [RepresentationTheory.KPCompactHarmonicTruncation.rawSymmetricPowerTrace,
      KPCompactHarmonic.symmetricPowerTrace, h, h']
private theorem char_eq (n : ℕ) (k : ComplexSU2) :
    su2HarmonicCharacter n k = chebR n ((k.val.trace)^2) := by
  have h := rawRankOneCharacter_eq_chebR n
    (⟨k.val, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ :
      RepresentationTheory.KPCompactHarmonicTruncation.RawU2)
  simpa [su2HarmonicCharacter, RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter,
    KPCompactHarmonic.rankOneCharacter, raw_sym,
    (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2] using h
open scoped Matrix.Norms.Elementwise in
private theorem section_eval (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f g.val = f g := by
  unfold matrixFunction
  rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  exact Units.ext rfl
open scoped Matrix.Norms.Elementwise in
private theorem section_path (j : Fin 3) (s : ℝ) (f v : PrincipalSeries s) (hv : ∀ g, v g = compactRawDerivative j f g)
    (g : ComplexGL2) (k : ComplexSU2) (t : ℝ) :
    HasDerivAt (fun r => f (g * complexSU2Embedding (k * compactCurve j r)))
      (v (g * complexSU2Embedding (k * compactCurve j t))) t := by
  let q := g * complexSU2Embedding (k * compactCurve j t)
  have hf := ((principalSeries_mem_iff s f).mp f.property).2
  have hdiff := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage (by fun_prop : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det))).mem_nhds
      (Matrix.GeneralLinearGroup.det_ne_zero q))
  have he (r : ℝ) : ((g * complexSU2Embedding (k * compactCurve j r) : ComplexGL2) :
      Matrix (Fin 2) (Fin 2) ℂ) = g.val * k.val * (basisExp compactBasis compactBasis_skew (0,j) r).val := by
    simp [compactCurve, Matrix.GeneralLinearGroup.coe_mul, complexSU2Embedding, Matrix.mul_assoc]
  have hmat : HasDerivAt (fun r : ℝ => g.val * k.val * (basisExp compactBasis compactBasis_skew (0,j) r).val)
      (q.val * compactBasis 0 j) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro z
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
      (basisExp_hasDerivAt_entry compactBasis compactBasis_skew (0,j) t a z).const_mul ((g.val * k.val) i a)) using 1
    · rfl
    · change (q.val * compactBasis 0 j) i z =
        ((g.val * k.val) * ((basisExp compactBasis compactBasis_skew (0,j) t).val * compactBasis 0 j)) i z
      rw [← Matrix.mul_assoc, ← he]
  have hh := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq t hmat (he t)
  simp only [← he] at hh
  rw [hv]
  change HasDerivAt _ ((fderiv ℝ (matrixFunction f) q.val) (q.val * compactBasis 0 j)) t
  convert hh using 1
  · funext r
    exact (section_eval f _).symm
  · rfl
noncomputable def charP (n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := star (chebR n (m.trace ^ 2))
open scoped Matrix.Norms.Elementwise in
private theorem charP_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (charP n) := by
  apply (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.trace) := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    fun_prop
  exact (cheb_smooth n).1.comp (ht.pow 2)
open scoped Matrix.Norms.Elementwise in
noncomputable def weightD (j : Fin 3) (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (m : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := fderiv ℝ P m (m * compactBasis 0 j)
open scoped Matrix.Norms.Elementwise in
private theorem weightD_smooth (j : Fin 3) (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) : ContDiff ℝ (⊤ : ℕ∞) (weightD j P) := by
  apply (hP.fderiv_right (by simp)).clm_apply
  change ContDiff ℝ (⊤ : ℕ∞) (fun m : Matrix (Fin 2) (Fin 2) ℂ => fun i k => ∑ a, m i a * compactBasis 0 j a k)
  fun_prop
open scoped Matrix.Norms.Elementwise in
private theorem weight_path (j : Fin 3) (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (k : ComplexSU2) (t : ℝ) :
    HasDerivAt (fun r => P (k * compactCurve j r).val) (weightD j P (k * compactCurve j t).val) t := by
  have hmat : HasDerivAt (fun r : ℝ => (k * compactCurve j r).val)
      ((k * compactCurve j t).val * compactBasis 0 j) t := by
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
      (basisExp_hasDerivAt_entry compactBasis compactBasis_skew (0,j) t c b).const_mul (k.val a c)) using 1
    · rfl
    · change ((k.val * (basisExp compactBasis compactBasis_skew (0,j) t).val) * compactBasis 0 j) a b =
        (k.val * ((basisExp compactBasis compactBasis_skew (0,j) t).val * compactBasis 0 j)) a b
      rw [Matrix.mul_assoc]
  convert (hP.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hmat using 1 <;> rfl
private theorem compactCurve_unitary (j : Fin 3) (t : ℝ) :
    (⟨(compactCurve j t).val, (Matrix.mem_specialUnitaryGroup_iff.mp (compactCurve j t).property).1⟩ :
      RepresentationTheory.KPCompactHarmonicTruncation.RawU2) = basisExp compactBasis compactBasis_skew (0,j) t := rfl
private theorem char_raw (n : ℕ) (k : ComplexSU2) :
    RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter n
      ⟨k.val, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ = su2HarmonicCharacter n k := by
  simp only [RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter, KPCompactHarmonic.rankOneCharacter,
    su2HarmonicCharacter, raw_sym]
open scoped Matrix.Norms.Elementwise in
private theorem second_weight (n : ℕ) (j : Fin 3) (k : ComplexSU2) :
    compactCharacterSecondDerivative n j k = weightD j (weightD j (charP n)) k.val := by
  have he (t r : ℝ) :
      star (RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter n
        (⟨k.val, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ *
          basisExp compactBasis compactBasis_skew (0,j) t *
          basisExp compactBasis compactBasis_skew (0,j) r)) =
        charP n ((k * compactCurve j t) * compactCurve j r).val := by
    rw [← compactCurve_unitary j t, ← compactCurve_unitary j r]
    rw [show (⟨k.val, (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ *
        ⟨(compactCurve j t).val, (Matrix.mem_specialUnitaryGroup_iff.mp (compactCurve j t).property).1⟩ *
        ⟨(compactCurve j r).val, (Matrix.mem_specialUnitaryGroup_iff.mp (compactCurve j r).property).1⟩ :
          RepresentationTheory.KPCompactHarmonicTruncation.RawU2) =
        ⟨((k * compactCurve j t) * compactCurve j r).val,
          (Matrix.mem_specialUnitaryGroup_iff.mp (((k * compactCurve j t) * compactCurve j r).property)).1⟩ from rfl]
    rw [char_raw, char_eq]
    rfl
  unfold compactCharacterSecondDerivative rankOneSecondDerivative
  simp_rw [he, (weight_path j (charP n) (charP_smooth n) (k * compactCurve j _) 0).deriv]
  have hz : compactCurve j 0 = 1 := by
    apply Subtype.ext
    change (basisExp compactBasis compactBasis_skew (0,j) 0).val = (1 : Matrix (Fin 2) (Fin 2) ℂ)
    simpa using congrArg (fun u : RepresentationTheory.KPCompactHarmonicTruncation.RawU2 => u.val)
      (basisExp_zero compactBasis compactBasis_skew (0,j))
  simp only [hz, mul_one]
  exact (weight_path j (weightD j (charP n)) (weightD_smooth j _ (charP_smooth n)) k 0).deriv.trans (by rw [hz, mul_one])
private theorem curve_zero (j : Fin 3) : compactCurve j 0 = 1 := by
  apply Subtype.ext
  change (basisExp compactBasis compactBasis_skew (0,j) 0).val = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  simpa using congrArg (fun u : RepresentationTheory.KPCompactHarmonicTruncation.RawU2 => u.val)
    (basisExp_zero compactBasis compactBasis_skew (0,j))
private theorem curve_neg (j : Fin 3) (t : ℝ) : compactCurve j (-t) = (compactCurve j t)⁻¹ := by
  rw [← Matrix.star_eq_inv]
  apply Subtype.ext
  change NormedSpace.exp (((-t : ℝ) : ℂ) • compactBasis 0 j) =
    star (NormedSpace.exp ((t : ℂ) • compactBasis 0 j))
  rw [NormedSpace.star_exp]
  simp [compactBasis_skew]
private theorem first_transfer
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulRightInvariant]
    (c : ℝ → K) (hc : Continuous c) (hc0 : c 0 = 1)
    (hcneg : ∀ t, c (-t) = (c t)⁻¹)
    (a da b db : K → ℂ) (ha : Continuous a) (hda : Continuous da)
    (hb : Continuous b) (hdb : Continuous db)
    (hda' : ∀ t k, HasDerivAt (fun r => a (k * c r)) (da (k * c t)) t)
    (hdb' : ∀ t k, HasDerivAt (fun r => b (k * c r)) (db (k * c t)) t) :
    (∫ k, a k * db k ∂μ) = -(∫ k, da k * b k ∂μ) := by
  have hleft := compact_parameter_integral_hasDerivAt μ
    (fun t k => a (k * c t) * b k) (fun t k => da (k * c t) * b k)
    ((ha.comp (continuous_snd.mul (hc.comp continuous_fst))).mul (hb.comp continuous_snd))
    ((hda.comp (continuous_snd.mul (hc.comp continuous_fst))).mul (hb.comp continuous_snd))
    (fun t k => (hda' t k).mul_const (b k)) 0
  have hright := compact_parameter_integral_hasDerivAt μ
    (fun t k => a k * b (k * c t)) (fun t k => a k * db (k * c t))
    ((ha.comp continuous_snd).mul (hb.comp (continuous_snd.mul (hc.comp continuous_fst))))
    ((ha.comp continuous_snd).mul (hdb.comp (continuous_snd.mul (hc.comp continuous_fst))))
    (fun t k => (hdb' t k).const_mul (a k)) 0
  have hn := hright.2.scomp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (neg_zero.symm)
  have heq : (fun t => ∫ k, a (k * c t) * b k ∂μ) =
      (fun t => ∫ k, a k * b (k * c (-t)) ∂μ) := by
    funext t
    have h := integral_mul_right_eq_self (μ := μ)
      (fun k => a k * b (k * c (-t))) (c t)
    simpa only [hcneg, mul_inv_cancel_right] using h
  rw [heq] at hleft
  have h := hleft.2.unique hn
  simp only [hc0, mul_one, neg_smul, one_smul, neg_zero] at h
  calc
    _ = - (-(∫ k, a k * db k ∂μ)) := (neg_neg _).symm
    _ = _ := congrArg Neg.neg h.symm
open scoped Matrix.Norms.Elementwise in
private theorem section_cont (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2) :
    Continuous (fun k : ComplexSU2 => f (g * complexSU2Embedding k)) := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2.continuousOn
  have hm : Continuous (fun k : ComplexSU2 => ((g * complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    change Continuous (fun k : ComplexSU2 => g.val * k.val)
    fun_prop
  have hc := hf.comp_continuous hm (fun k => Matrix.GeneralLinearGroup.det_ne_zero (g * complexSU2Embedding k))
  simpa only [Function.comp_def, section_eval] using hc
open scoped Matrix.Norms.Elementwise in

theorem characterAverage_compact_second_derivative_transfer
    (s : ℝ) (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ : ℕ) (j : Fin 3) (f v w : PrincipalSeries s)
    (hv : ∀ g, v g = compactRawDerivative j f g)
    (hw : ∀ g, w g = compactRawDerivative j v g) (g : ComplexGL2) :
    characterAverage s μ ℓ w g =
      ((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
        compactCharacterSecondDerivative ℓ j k * f (g * complexSU2Embedding k) ∂μ := by
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  letI : ContinuousInv ComplexSU2 := ⟨by
    apply continuous_induced_rng.mpr
    change Continuous (fun k : ComplexSU2 => star k.val)
    exact continuous_star.comp continuous_subtype_val⟩
  letI : IsTopologicalGroup ComplexSU2 := {}
  letI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  letI : SecondCountableTopology ComplexSU2 := Topology.IsInducing.subtypeVal.secondCountableTopology
  letI : μ.IsHaarMeasure := hhaar
  letI : IsProbabilityMeasure μ := hprob
  letI : μ.IsMulRightInvariant := ⟨fun k =>
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map (· * k)) μ⟩
  have hc : Continuous (compactCurve j) := by
    apply Continuous.subtype_mk
    change Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • compactBasis 0 j))
    exact (differentiable_exp_smul_const ℂ _).continuous.comp Complex.continuous_ofReal
  let a := fun k : ComplexSU2 => charP ℓ k.val
  let da := fun k : ComplexSU2 => weightD j (charP ℓ) k.val
  let dda := fun k : ComplexSU2 => weightD j (weightD j (charP ℓ)) k.val
  have ha : Continuous a := (charP_smooth ℓ).continuous.comp continuous_subtype_val
  have hda : Continuous da := (weightD_smooth j _ (charP_smooth ℓ)).continuous.comp continuous_subtype_val
  have hdda : Continuous dda := (weightD_smooth j _ (weightD_smooth j _ (charP_smooth ℓ))).continuous.comp continuous_subtype_val
  have h₁ := first_transfer μ (compactCurve j) hc (curve_zero j) (curve_neg j)
    a da (fun k => v (g * complexSU2Embedding k)) (fun k => w (g * complexSU2Embedding k))
    ha hda (section_cont s v g) (section_cont s w g)
    (fun t k => weight_path j _ (charP_smooth ℓ) k t)
    (fun t k => section_path j s v w hw g k t)
  have h₂ := first_transfer μ (compactCurve j) hc (curve_zero j) (curve_neg j)
    da dda (fun k => f (g * complexSU2Embedding k)) (fun k => v (g * complexSU2Embedding k))
    hda hdda (section_cont s f g) (section_cont s v g)
    (fun t k => weight_path j _ (weightD_smooth j _ (charP_smooth ℓ)) k t)
    (fun t k => section_path j s f v hv g k t)
  rw [characterAverage_formula]
  congr 1
  have hechar (k : ComplexSU2) : star (su2HarmonicCharacter ℓ k) = a k := by
    rw [char_eq]; rfl
  simp_rw [hechar]
  rw [h₁, h₂, neg_neg]
  apply integral_congr_ae
  filter_upwards with k
  rw [second_weight]

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

private theorem rawSymmetricPowerTrace_eq_sym (n : ℕ)
    (u : RepresentationTheory.KPCompactHarmonicTruncation.RawU2) :
    RepresentationTheory.KPCompactHarmonicTruncation.rawSymmetricPowerTrace n u =
      KPCompactHarmonic.symmetricPowerTrace n u := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h0 h1 => simp only [RepresentationTheory.KPCompactHarmonicTruncation.rawSymmetricPowerTrace,
      KPCompactHarmonic.symmetricPowerTrace, h0, h1]

private theorem rawRankOneCharacter_eq_sym (ℓ : ℕ)
    (u : RepresentationTheory.KPCompactHarmonicTruncation.RawU2) :
    RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter ℓ u =
      KPCompactHarmonic.rankOneCharacter ℓ u := by
  rw [RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter, KPCompactHarmonic.rankOneCharacter,
    rawSymmetricPowerTrace_eq_sym]

private theorem compactBasis_trace (j : Fin 1) (a : Fin 3) :
    Matrix.trace (compactBasis j a) = 0 := by
  fin_cases a <;> simp [compactBasis, Matrix.trace, Fin.sum_univ_two]

private theorem compactBasis_orth (j : Fin 1) (a b : Fin 3) :
    -(Matrix.trace (compactBasis j a * compactBasis j b)).re = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [compactBasis, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.I_mul_I]
  all_goals nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

private theorem matrixFunction_eval_here (f : ComplexGL2 → ℂ) (g : ComplexGL2) :
    matrixFunction f (g : Matrix (Fin 2) (Fin 2) ℂ) = f g := by
  rw [matrixFunction, dif_pos (Matrix.GeneralLinearGroup.det_ne_zero g)]
  congr 1
  apply Units.ext
  rfl

private theorem orbit_continuous_here (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2) :
    Continuous (fun k : ComplexSU2 => f (g * complexSU2Embedding k)) := by
  have hf := ((principalSeries_mem_iff s f).mp f.property).2.continuousOn
  have hm : Continuous (fun k : ComplexSU2 =>
      ((g * complexSU2Embedding k : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    change Continuous (fun k : ComplexSU2 =>
      (g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))
    fun_prop
  have hc := hf.comp_continuous hm (fun k =>
    Matrix.GeneralLinearGroup.det_ne_zero (g * complexSU2Embedding k))
  simpa only [Function.comp_def, matrixFunction_eval_here] using hc

private theorem characterSecondDerivative_one_eq (ℓ : ℕ) (j : Fin 3) (k : ComplexSU2) :
    RepresentationTheory.KPCompactHarmonicTruncation.Casimir.characterSecondDerivative
        compactBasis compactBasis_skew (fun _ : Fin 1 => ℓ) (0, j)
        (fun _ => (⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ :
            RepresentationTheory.KPCompactHarmonicTruncation.RawU2)) =
      compactCharacterSecondDerivative ℓ j k := by
  rw [RepresentationTheory.KPCompactHarmonicTruncation.Casimir.characterSecondDerivative_factor]
  simp [compactCharacterSecondDerivative]

private theorem su2HarmonicCharacter_eq_raw (ℓ : ℕ) (k : ComplexSU2) :
    RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter ℓ
        (⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ :
            RepresentationTheory.KPCompactHarmonicTruncation.RawU2) =
      su2HarmonicCharacter ℓ k := by
  rw [su2HarmonicCharacter]
  exact rawRankOneCharacter_eq_sym ℓ _

theorem compactCharacter_integrated_laplacian (s : ℝ) (μ : Measure ComplexSU2)
    [IsFiniteMeasure μ] (ℓ : ℕ) (f : PrincipalSeries s) (g : ComplexGL2) :
    (∑ j : Fin 3, ((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
      compactCharacterSecondDerivative ℓ j k * f (g * complexSU2Embedding k) ∂μ) =
      -(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) * characterAverage s μ ℓ f g := by
  have hcompact : IsCompact (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq : Set.range (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ)) =
        (ComplexSU2 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := Subtype.range_coe
    rw [← heq]
    exact complexSU2_isCompact
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp hcompact
  have horbit : Continuous (fun k : ComplexSU2 => f (g * complexSU2Embedding k)) :=
    orbit_continuous_here s f g
  have hchar : Continuous (fun k : ComplexSU2 => su2HarmonicCharacter ℓ k) :=
    (ChartDerivativeBounds.su2_character_continuous_norm_bound ℓ).1
  have hD : ∀ j : Fin 3,
      Continuous (fun k : ComplexSU2 => compactCharacterSecondDerivative ℓ j k) := by
    intro j
    have hu : Continuous (fun k : ComplexSU2 =>
        (⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ :
            RepresentationTheory.KPCompactHarmonicTruncation.RawU2)) :=
      Continuous.subtype_mk continuous_subtype_val _
    have h := (RepresentationTheory.KPCompactHarmonicTruncation.Casimir.characterSecondDerivative_continuous
      compactBasis compactBasis_skew (fun _ : Fin 1 => ℓ) (0, j)).comp
        (continuous_pi (fun _ => hu))
    exact h.congr (fun k => characterSecondDerivative_one_eq ℓ j k)
  have hIntD : ∀ j : Fin 3, Integrable (fun k : ComplexSU2 =>
      compactCharacterSecondDerivative ℓ j k * f (g * complexSU2Embedding k)) μ := fun j =>
    ((hD j).mul horbit).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntχ : Integrable (fun k : ComplexSU2 =>
      star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k)) μ :=
    ((hchar.star).mul horbit).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ k : ComplexSU2, (∑ j : Fin 3, compactCharacterSecondDerivative ℓ j k) =
      -(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) * star (su2HarmonicCharacter ℓ k) := by
    intro k
    have h := RepresentationTheory.KPCompactHarmonicTruncation.Casimir.rankOneSecondDerivative_sum
      compactBasis compactBasis_skew compactBasis_trace compactBasis_orth ℓ (0 : Fin 1)
      (⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
        (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ :
          RepresentationTheory.KPCompactHarmonicTruncation.RawU2)
    have h' : (∑ j : Fin 3, compactCharacterSecondDerivative ℓ j k) =
        -(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) *
          star (RepresentationTheory.KPCompactHarmonicTruncation.rawRankOneCharacter ℓ
            (⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
              (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩ :
                RepresentationTheory.KPCompactHarmonicTruncation.RawU2)) := h
    rw [h', su2HarmonicCharacter_eq_raw]
  rw [characterAverage_formula]
  calc
    (∑ j : Fin 3, ((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
        compactCharacterSecondDerivative ℓ j k * f (g * complexSU2Embedding k) ∂μ)
        = ((2 * ℓ + 1 : ℕ) : ℂ) * ∑ j : Fin 3, ∫ k : ComplexSU2,
            compactCharacterSecondDerivative ℓ j k * f (g * complexSU2Embedding k) ∂μ := by
          rw [Finset.mul_sum]
    _ = ((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
          ∑ j : Fin 3, compactCharacterSecondDerivative ℓ j k *
            f (g * complexSU2Embedding k) ∂μ := by
          congr 1
          exact (integral_finsetSum Finset.univ (fun j _ => hIntD j)).symm
    _ = ((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
          (∑ j : Fin 3, compactCharacterSecondDerivative ℓ j k) *
            f (g * complexSU2Embedding k) ∂μ := by
          congr 1
          apply integral_congr_ae
          filter_upwards with k
          rw [Finset.sum_mul]
    _ = ((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
          (-(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) * star (su2HarmonicCharacter ℓ k)) *
            f (g * complexSU2Embedding k) ∂μ := by
          congr 1
          apply integral_congr_ae
          filter_upwards with k
          rw [hpt k]
    _ = ((2 * ℓ + 1 : ℕ) : ℂ) *
          (-(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) * ∫ k : ComplexSU2,
            star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k) ∂μ) := by
          congr 1
          rw [show (fun k : ComplexSU2 =>
                (-(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) * star (su2HarmonicCharacter ℓ k)) *
                  f (g * complexSU2Embedding k))
              = (fun k : ComplexSU2 => -(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) *
                  (star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k))) from by
                funext k; ring]
          rw [integral_const_mul]
    _ = -(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) *
          (((2 * ℓ + 1 : ℕ) : ℂ) * ∫ k : ComplexSU2,
            star (su2HarmonicCharacter ℓ k) * f (g * complexSU2Embedding k) ∂μ) := by ring

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open scoped Matrix.Norms.Elementwise

open scoped Matrix.Norms.Operator in

noncomputable def matExp (M : Matrix (Fin 2) (Fin 2) ℂ) : ComplexGL2 :=
  (NormedSpace.isUnit_exp M).unit

private theorem matExp_coe (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ((matExp M : ComplexGL2) : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp M :=
  IsUnit.unit_spec _

open scoped Matrix.Norms.Operator in
private theorem matrix_path_diff (g : ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, DifferentiableAt ℝ
      (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp ((t : ℂ) • M)) i j) 0 := by
  have hmat : DifferentiableAt ℝ
      (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp ((t : ℂ) • M)) 0 := by
    exact (differentiableAt_const _).mul
      ((differentiable_exp_smul_const ℂ M).differentiableAt.restrictScalars ℝ |>.comp 0
        Complex.ofRealCLM.differentiableAt)
  intro i j
  exact (ContinuousLinearMap.proj j).differentiableAt.comp 0
    ((ContinuousLinearMap.proj i).differentiableAt.comp 0 hmat)

open scoped Matrix.Norms.Operator in
private theorem matrix_path_hasDeriv_components (g : ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ i j, HasDerivAt
      (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp ((t : ℂ) • M)) i j)
      (((g : Matrix (Fin 2) (Fin 2) ℂ) * M) i j) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) M ((0 : ℝ) : ℂ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    (f := fun t : ℝ => (t : ℂ)) 0 Complex.ofRealCLM.hasDerivAt
  have hmat := h.const_mul (g : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one,
    ContinuousLinearMap.coe_restrictScalars,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul,
    NormedSpace.exp_zero, mul_one, one_mul] at hmat
  intro i j
  have hi := (ContinuousLinearMap.proj i :
    Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Fin 2 → ℂ).hasFDerivAt.comp_hasDerivAt 0 hmat
  have hj := (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt
    (fun t : ℝ => ((g : Matrix (Fin 2) (Fin 2) ℂ) *
      NormedSpace.exp ((t : ℂ) • M)) i j)
    (((g : Matrix (Fin 2) (Fin 2) ℂ) *
      (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ
          (NormedSpace.exp (((0 : ℝ) : ℂ) • M) * M))) 1) i j) 0 at hj
  simpa using hj

private theorem path_eq (s : ℝ) (f : PrincipalSeries s) (g : ComplexGL2)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (fun t : ℝ => f (g * matExp ((t : ℂ) • M))) =
      matrixFunction f.val ∘
        (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) *
          NormedSpace.exp ((t : ℂ) • M)) := by
  funext t
  have hu := Matrix.GeneralLinearGroup.det_ne_zero (g * matExp ((t : ℂ) • M))
  have he : ((g * matExp ((t : ℂ) • M)) : Matrix (Fin 2) (Fin 2) ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) * NormedSpace.exp ((t : ℂ) • M) := by
    rw [matExp_coe]
  dsimp only [Function.comp_def]
  rw [← he]
  unfold KPCplxPrincipalSeriesCharts.matrixFunction
  rw [dif_pos (show ((g : Matrix (Fin 2) (Fin 2) ℂ) *
    (matExp ((t : ℂ) • M) : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 from by
      simpa only [Units.val_mul] using hu)]
  apply congrArg f.val
  apply Units.ext
  rfl

private theorem path_differentiable (s : ℝ) (f : PrincipalSeries s)
    (g : ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    DifferentiableAt ℝ (fun t : ℝ => f (g * matExp ((t : ℂ) • M))) 0 := by
  have hf := ((principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : DifferentiableAt ℝ
      (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp ((t : ℂ) • M)) 0 :=
    differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (matrix_path_diff g M i))
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ) *
      NormedSpace.exp (((0 : ℝ) : ℂ) • M)).det ≠ 0 := by
    simpa using Matrix.GeneralLinearGroup.det_ne_zero g
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds hdet)
  have hc := hh.comp 0 hmat
  convert hc using 1
  exact path_eq s f g M

private theorem raw_derivative_eq (s : ℝ) (f : PrincipalSeries s)
    (g : ComplexGL2) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    deriv (fun t : ℝ => f (g * matExp ((t : ℂ) • M))) 0 =
      fderiv ℝ (matrixFunction f.val) (g : Matrix (Fin 2) (Fin 2) ℂ)
        ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) := by
  have hf := ((principalSeries_mem_iff s f.val).mp f.property).2
  have hmat : HasDerivAt
      (fun t : ℝ => (g : Matrix (Fin 2) (Fin 2) ℂ) *
        NormedSpace.exp ((t : ℂ) • M))
      ((g : Matrix (Fin 2) (Fin 2) ℂ) * M) 0 :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (matrix_path_hasDeriv_components g M i))
  have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
  have hh := (hf.differentiableOn (by simp)).differentiableAt
    ((isOpen_ne.preimage hcont).mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hc := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hmat (by simp)
  rw [path_eq s f g M]
  exact hc.deriv

private theorem local_derivative_mem (s : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (f : PrincipalSeries s) :
    (fun g => deriv (fun t : ℝ => f (g * matExp ((t : ℂ) • M))) 0) ∈
      principalSeriesSubmodule s := by
  apply (principalSeries_mem_iff s _).mpr
  constructor
  · intro a d b g
    have he : (fun t : ℝ => f (upperTriangular a d b * g * matExp ((t : ℂ) • M))) =
        (fun t : ℝ => (inductionWeight s a d : ℂ) •
          f (g * matExp ((t : ℂ) • M))) := by
      funext t
      rw [mul_assoc]
      exact f.property.1 a d b _
    dsimp only
    rw [he]
    exact deriv_const_smul (inductionWeight s a d : ℂ)
      (path_differentiable s f g M)
  · have hf := ((principalSeries_mem_iff s f.val).mp f.property).2
    have hcont : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by fun_prop
    have hs : IsOpen {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} :=
      isOpen_ne.preimage hcont
    have hd := hf.fderiv_of_isOpen hs (m := (⊤ : ℕ∞)) (by simp)
    have hm : ContDiff ℝ (⊤ : ℕ∞)
        (fun m : Matrix (Fin 2) (Fin 2) ℂ => m * M) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun m : Matrix (Fin 2) (Fin 2) ℂ => fun i j => ∑ k, m i k * M k j)
      fun_prop
    apply (hd.clm_apply hm.contDiffOn).congr
    intro m hm
    unfold KPCplxPrincipalSeriesCharts.matrixFunction
    rw [dif_pos (show m.det ≠ 0 from hm)]
    exact raw_derivative_eq s f (Matrix.GeneralLinearGroup.mkOfDetNeZero m hm) M

theorem compactRawDerivative_section_exists (s : ℝ) (j : Fin 3)
    (f : PrincipalSeries s) :
    ∃ v : PrincipalSeries s, ∀ g, v g = compactRawDerivative j f g := by
  refine ⟨⟨fun g => deriv (fun t : ℝ => f (g * matExp ((t : ℂ) • compactBasis 0 j))) 0,
    local_derivative_mem s (compactBasis 0 j) f⟩, ?_⟩
  intro g
  show deriv (fun t : ℝ => f (g * matExp ((t : ℂ) • compactBasis 0 j))) 0 =
    compactRawDerivative j f g
  unfold compactRawDerivative
  exact raw_derivative_eq s f g (compactBasis 0 j)

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer.Transfer

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory

theorem exists_shiftedCasimir_transfer_section (s : ℝ) (f : PrincipalSeries s) :
    ∃ w : PrincipalSeries s, ∀ (μ : Measure ComplexSU2),
      μ.IsHaarMeasure → IsProbabilityMeasure μ → ∀ (ℓ : ℕ) (g : ComplexGL2),
        characterAverage s μ ℓ w g =
          (((1 + (ℓ : ℝ) * (ℓ + 1) : ℝ) : ℂ) * characterAverage s μ ℓ f g) := by
  classical
  let v : Fin 3 → PrincipalSeries s := fun j =>
    (Transfer.compactRawDerivative_section_exists s j f).choose
  have hv (j : Fin 3) (g : ComplexGL2) :
      v j g = Transfer.compactRawDerivative j f g :=
    (Transfer.compactRawDerivative_section_exists s j f).choose_spec g
  let u : Fin 3 → PrincipalSeries s := fun j =>
    (Transfer.compactRawDerivative_section_exists s j (v j)).choose
  have hu (j : Fin 3) (g : ComplexGL2) :
      u j g = Transfer.compactRawDerivative j (v j) g :=
    (Transfer.compactRawDerivative_section_exists s j (v j)).choose_spec g
  refine ⟨f - (1 / 2 : ℂ) • ∑ j : Fin 3, u j, ?_⟩
  intro μ hhaar hprob ℓ g
  letI : IsProbabilityMeasure μ := hprob
  obtain ⟨A, hA⟩ := Transfer.characterAverage_linear_exists s μ ℓ g
  have hsum : A (∑ j : Fin 3, u j) =
      -(2 * (ℓ : ℂ) * ((ℓ : ℂ) + 1)) * A f := by
    rw [map_sum]
    simp only [hA]
    simp_rw [Transfer.characterAverage_compact_second_derivative_transfer
      s μ hhaar hprob ℓ _ f _ _ (hv _) (hu _) g]
    exact Transfer.compactCharacter_integrated_laplacian s μ ℓ f g
  rw [← hA, map_sub, map_smul, hsum, hA]
  push_cast
  ring

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CasimirTransfer

end
