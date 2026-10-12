module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.MeasurableFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContActualCotangentPlaceProjection

open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

section BlockCalculus

open scoped ContDiff
open Topology
open KPContCotangentRealOrthogonalComplexification

private theorem action_diff (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    ContDiff ℝ ∞ (KPArch.action g) := by
  have h := (KPArch.productAction_contDiff 1 (fun _ => g)).of_le
    (show (∞ : WithTop ℕ∞) ≤ ⊤ from le_top)
  exact (contDiff_apply ℝ KPArch.H3 (0 : Fin 1)).comp
    (h.comp (show ContDiff ℝ ∞ (fun z : KPArch.H3 => (fun _ : Fin 1 => z)) by fun_prop))
private theorem product_deriv (n : ℕ) (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (z v : KPArch.Space n) (i : Fin n) (hv : v i = 0) :
    (fderiv ℝ (KPArch.productAction n g) z v) i = 0 := by
  have ha (i : Fin n) : DifferentiableAt ℝ (KPArch.action (g i)) (z i) :=
    (action_diff (g i)).differentiable (by simp) (z i)
  have hp : fderiv ℝ (KPArch.productAction n g) z =
      ContinuousLinearMap.pi (fun i =>
        (fderiv ℝ (KPArch.action (g i)) (z i)).comp (ContinuousLinearMap.proj i)) := by
    unfold KPArch.productAction
    change fderiv ℝ (fun z : KPArch.Space n => fun i => (KPArch.action (g i) ∘ (fun z : KPArch.Space n => z i)) z) z = _
    rw [fderiv_pi (fun i => (ha i).comp z (differentiableAt_apply i z))]
    congr 1
    funext i
    rw [fderiv_comp z (ha i) (differentiableAt_apply i z)]
    congr 1
    exact (ContinuousLinearMap.proj i : KPArch.Space n →L[ℝ] KPArch.H3).hasFDerivAt.fderiv
  rw [hp]
  simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, hv]
private theorem coframe_zero (n : ℕ) (p v : HyperbolicChart.Space n) (i : Fin n)
    (hv : ∀ k, v (i,k) = 0) : ∀ k, CotangentLogCoframe.C n p v (i,k) = 0 := by
  intro k
  fin_cases k <;> simp [CotangentLogCoframe.C, hv]
private theorem A_zero (n : ℕ) (v : HyperbolicChart.Space n) (i : Fin n)
    (hv : ∀ k, v (i,k) = 0) : CotangentLogCoframe.A n v i = 0 := by
  simp [CotangentLogCoframe.A_apply, hv]
private theorem Ainv_zero (n : ℕ) (v : KPArch.Space n) (i : Fin n)
    (hv : v i = 0) : ∀ k, (CotangentLogCoframe.A n).symm v (i,k) = 0 := by
  intro k
  fin_cases k <;> simp [CotangentLogCoframe.A, hv]
private theorem H_basis_zero (n : ℕ) (p : HyperbolicChart.Space n) (i j : Fin n)
    (hij : i ≠ j) (l : Fin 3) : ∀ k,
      CotangentLogCoframe.H n p (EuclideanSpace.basisFun (Fin n × Fin 3) ℝ (j,l)) (i,k) = 0 := by
  intro k
  have hne : ∀ k : Fin 3, (i,k) ≠ (j,l) := fun k h => hij (congrArg Prod.fst h)
  fin_cases k <;> simp [CotangentLogCoframe.H, CotangentLogCoframe.C, EuclideanSpace.basisFun_apply, hne, hij]

private theorem formula_deriv_zero (n : ℕ) (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (p v : HyperbolicChart.Space n) (i : Fin n) (hv : ∀ k, v (i,k) = 0) : ∀ k,
    fderiv ℝ (fun x => (CotangentLogCoframe.A n).symm
      (KPArch.productAction n g (CotangentLogCoframe.A n x))) p v (i,k) = 0 := by
  have hd := (CotangentLogCoframe.A n).symm.hasFDerivAt.comp p
    (((KPArch.productAction_contDiff n g).differentiable (by simp)
      (CotangentLogCoframe.A n p)).hasFDerivAt.comp p (CotangentLogCoframe.A n).hasFDerivAt)
  change HasFDerivAt (fun x => (CotangentLogCoframe.A n).symm
    (KPArch.productAction n g (CotangentLogCoframe.A n x))) _ p at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  apply Ainv_zero
  apply product_deriv
  exact A_zero n v i hv

private theorem Q_block {c : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F:=F) (ζ:=ζ) (hζ:=hζ) (U:=U) (H:=H) c}
    (e : Arrow a b) (hab : b.places = a.places) (x : M F) (hx : x ∈ e.domain)
    (i j : Fin (d F)) (hij : i ≠ j) (k l : Fin 3) :
    Q e x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ (j,l)) (i,k) = 0 := by
  obtain ⟨g, -, hg⟩ := actual_local_formula e
  have heq : e.psi =ᶠ[𝓝 x] (fun y => (CotangentLogCoframe.A (d F)).symm
      (KPArch.productAction (d F) g (CotangentLogCoframe.A (d F) y))) := by
    filter_upwards [e.isOpen_domain.mem_nhds hx] with y hy
    have hh := hg hy
    rw [hab, Equiv.self_trans_symm] at hh
    exact hh
  unfold Q
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  apply coframe_zero
  rw [heq.fderiv_eq]
  apply formula_deriv_zero
  exact H_basis_zero (d F) x i j hij l

 def mask (i : Fin (d F)) (v : E F) : E F :=
  WithLp.toLp 2 (fun jk => if jk.1 = i then v jk else 0)
 theorem T_mask {c : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F:=F) (ζ:=ζ) (hζ:=hζ) (U:=U) (H:=H) c}
    (e : Arrow a b) (hab : b.places = a.places) (x : M F) (hx : x ∈ e.domain)
    (i : Fin (d F)) (v : E F) : T e x hx (mask i v) = mask i (T e x hx v) := by
  ext jk
  obtain ⟨j,k⟩ := jk
  change (e.phase x • operatorComplexification _ (Q e x) (mask i v)) (j,k) = _
  change e.phase x * (operatorComplexification _ (Q e x) (mask i v)) (j,k) =
    if j = i then e.phase x * (operatorComplexification _ (Q e x) v) (j,k) else 0
  rw [operatorComplexification_apply, operatorComplexification_apply]
  by_cases hji : j = i
  · simp only [hji, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro lk hlk
    obtain ⟨l,m⟩ := lk
    by_cases hli : l = i
    · simp [mask, hli]
    · rw [Q_block e hab x hx i l (Ne.symm hli) k m]
      simp
  · simp only [hji, ite_false]
    have hz : ∀ lm : Fin (d F) × Fin 3,
        (↑((Q e x (EuclideanSpace.basisFun (Fin (d F) × Fin 3) ℝ lm)) (j,k)) : ℂ) * mask i v lm = 0 := by
      rintro ⟨l,m⟩
      by_cases hli : l = i
      · rw [Q_block e hab x hx j l (by simpa [hli] using hji) k m]
        simp
      · simp [mask, hli]
    rw [Finset.sum_eq_zero (fun lm _ => hz lm), mul_zero]
private theorem cast_places {i j : Fin (H.atlas U).componentCount} (h : i = j)
    (s : LiftedChart (F:=F) (ζ:=ζ) (hζ:=hζ) (U:=U) (H:=H) i) :
    (h ▸ s).places = s.places := by
  cases h
  rfl
 theorem target_places (a b : ShrunkChart F ζ hζ U R P H) (h : a.component = b.component) :
    (targetChart a b h).places = (isotropyChart a).places := by
  unfold targetChart
  rw [cast_places]
  rfl

end BlockCalculus

def project (i : Fin (d F)) :
    Family (U := U) (H := H) →ₗ[ℂ] Family (U := U) (H := H) where
  toFun W := ⟨fun a x => WithLp.toLp 2
    (fun jk => if jk.1 = i then coefficient W a x jk else 0), by
      refine ⟨?_, ?_, ?_⟩
      · intro a
        apply (WithLp.measurable_toLp 2 _).comp
        apply measurable_pi_lambda
        intro jk
        by_cases hji : jk.1 = i
        · simp only [hji, ite_true]
          exact ((EuclideanSpace.proj jk : E F →L[ℂ] ℂ).continuous.measurable).comp
            (W.property.1 a)
        · simp only [hji, ite_false]
          exact measurable_const
      · intro a γ x hx
        change mask i _ = T (isotropyArrow a γ) x (omega_subset_larger a hx) (mask i _)
        exact (congrArg (mask i) (W.property.2.1 a γ x hx)).trans
          (T_mask (isotropyArrow a γ) rfl x (omega_subset_larger a hx) i _).symm
      · intro a b e x hx
        change mask i _ = T e.arrow x hx (mask i _)
        exact (congrArg (mask i) (W.property.2.2 a b e x hx)).trans
          (T_mask e.arrow (target_places a b e.component_eq) x hx i _).symm⟩
  map_add' := by
    intro V W
    apply Subtype.ext
    funext a x
    ext jk
    simp only [coefficient]
    by_cases h : jk.1 = i <;> simp [h]
  map_smul' := by
    intro c W
    apply Subtype.ext
    funext a x
    ext jk
    simp only [coefficient]
    by_cases h : jk.1 = i <;> simp [h]

theorem coefficient_project (i : Fin (d F)) (W : Family (U := U) (H := H))
    (a : Chart (U := U) (H := H)) (x : omega a) (j : Fin (d F)) (k : Fin 3) :
    coefficient (project i W) a x (j, k) =
      if j = i then coefficient W a x (j, k) else 0 := by
  rfl

end DedekindZetaZeroFree.KPContActualCotangentPlaceProjection

end
