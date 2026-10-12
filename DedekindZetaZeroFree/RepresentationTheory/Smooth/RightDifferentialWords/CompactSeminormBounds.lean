module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.PositiveNativeCharts
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.RightInvariantFieldCoordinates

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped NumberField Classical BigOperators Topology

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordSeminorm

section FieldExpansion
open RightFrame.PullbackWords
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] {A : Type*}

private theorem word_smooth (O : Set E) (hO : IsOpen O) (fields : A → E → E)
    (hfields : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fields a) O)
    (w : List A) (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord fields w u) O := by
  induction w with
  | nil => exact hu
  | cons a w ih =>
    exact (ih.fderiv_of_isOpen hO (by simp)).clm_apply (hfields a)

private theorem sum_derivative {T : Type*} (ts : List T) (f : T → E → ℂ)
    (x : E) (hf : ∀ t ∈ ts, DifferentiableAt ℝ (f t) x) :
    HasFDerivAt (fun y => (ts.map (fun t => f t y)).sum)
      (ts.map (fun t => fderiv ℝ (f t) x)).sum x := by
  induction ts with
  | nil => simpa using hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x
  | cons t ts ih =>
    exact (hf t (by simp)).hasFDerivAt.fun_add (ih (fun r hr => hf r (by simp [hr])))

 theorem list_expansion (O : Set E) (hO : IsOpen O)
    (fields : A → E → E) (hfields : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (fields a) O)
    (w : List A) :
    let e := Module.finBasis ℝ E
    ∃ ts : List ((E → ℝ) × List (Fin (Module.finrank ℝ E))),
      (∀ t ∈ ts, ContDiffOn ℝ (⊤ : ℕ∞) t.1 O) ∧
      ∀ u : E → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u O → ∀ x ∈ O,
        directionalWord fields w u x =
          (ts.map (fun t => t.1 x • directionalWord (fun b _ => e b) t.2 u x)).sum := by
  classical
  dsimp only
  let e := Module.finBasis ℝ E
  let basisFields := fun b (_ : E) => e b
  have hbf : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (basisFields b) O := fun _ => contDiffOn_const
  induction w with
  | nil =>
    refine ⟨[(fun _ => 1, [])], ?_, ?_⟩
    · intro t ht; simp only [List.mem_singleton] at ht; subst t; exact contDiffOn_const
    · intro u hu x hx; simp [directionalWord]
  | cons a w ih =>
    obtain ⟨ts, hts, heq⟩ := ih
    let coeff : Fin (Module.finrank ℝ E) → E → ℝ := fun b x => e.repr (fields a x) b
    have hcoeff b : ContDiffOn ℝ (⊤ : ℕ∞) (coeff b) O :=
      (e.coord b).toContinuousLinearMap.contDiff.comp_contDiffOn (hfields a)
    let expand : ((E → ℝ) × List (Fin (Module.finrank ℝ E))) →
        List ((E → ℝ) × List (Fin (Module.finrank ℝ E))) := fun t =>
      (fun x => fderiv ℝ t.1 x (fields a x), t.2) ::
      Finset.univ.toList.map (fun b => (fun x => t.1 x * coeff b x, b :: t.2))
    refine ⟨ts.flatMap expand, ?_, ?_⟩
    · intro t ht
      obtain ⟨r, hr, ht⟩ := List.mem_flatMap.mp ht
      simp only [expand, List.mem_cons, List.mem_map] at ht
      rcases ht with rfl | ⟨b, hb, rfl⟩
      · exact ((hts r hr).fderiv_of_isOpen hO (by simp)).clm_apply (hfields a)
      · exact (hts r hr).mul (hcoeff b)
    · intro u hu x hx
      have he : directionalWord fields w u =ᶠ[𝓝 x]
          (fun y => (ts.map (fun t => t.1 y • directionalWord basisFields t.2 u y)).sum) :=
        Filter.Eventually.mono (hO.mem_nhds hx) (fun y hy => heq u hu y hy)
      change fderiv ℝ (directionalWord fields w u) x (fields a x) = _
      rw [he.fderiv_eq]
      have ht (t) (hm : t ∈ ts) : DifferentiableAt ℝ
          (fun y => t.1 y • directionalWord basisFields t.2 u y) x :=
        (((hts t hm).smul (word_smooth O hO basisFields hbf t.2 u hu)).contDiffAt
          (hO.mem_nhds hx)).differentiableAt (by simp)
      rw [(sum_derivative ts _ x ht).fderiv]
      have hterm (t) (hm : t ∈ ts) :
          fderiv ℝ (fun y => t.1 y • directionalWord basisFields t.2 u y) x (fields a x) =
          ((expand t).map (fun r => r.1 x • directionalWord basisFields r.2 u x)).sum := by
        have hc := ((hts t hm).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
        have hd := ((word_smooth O hO basisFields hbf t.2 u hu).contDiffAt
          (hO.mem_nhds hx)).differentiableAt (by simp)
        change fderiv ℝ (t.1 • directionalWord basisFields t.2 u) x (fields a x) = _
        rw [(hc.hasFDerivAt.smul hd.hasFDerivAt).fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.smul_apply]
        have hdecomp : fderiv ℝ (directionalWord basisFields t.2 u) x (fields a x) =
            ∑ b, e.repr (fields a x) b • fderiv ℝ (directionalWord basisFields t.2 u) x (e b) := by
          conv_lhs => arg 2; rw [← e.sum_repr (fields a x)]
          rw [map_sum]
          simp only [map_smul]
        rw [hdecomp]
        simp only [Finset.smul_sum, smul_smul]
        simp only [expand, List.map_cons, List.sum_cons, List.map_map,
          Function.comp_def, Finset.sum_toList, directionalWord, basisFields, coeff]
        rw [Finset.sum_map_toList]
        exact add_comm _ _
      rw [show ((ts.map (fun t => fderiv ℝ
          (fun y => t.1 y • directionalWord basisFields t.2 u y) x)).sum) (fields a x) =
          (ts.map (fun t => fderiv ℝ (fun y => t.1 y • directionalWord basisFields t.2 u y)
            x (fields a x))).sum by
        simpa only [List.map_map, Function.comp_def, ContinuousLinearMap.apply_apply] using
          map_list_sum (ContinuousLinearMap.apply ℝ ℂ (fields a x))
            (ts.map (fun t => fderiv ℝ (fun y => t.1 y • directionalWord basisFields t.2 u y) x))]
      rw [show (ts.flatMap expand).map (fun t => t.1 x • directionalWord (fun b _ => e b) t.2 u x) =
          (ts.map (fun t => (expand t).map (fun r => r.1 x • directionalWord basisFields r.2 u x))).flatten by
        simp [List.flatMap, List.map_flatten, List.map_map, Function.comp_def, basisFields]]
      rw [List.sum_flatten, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      exact hterm t ht

 theorem constant_word_iterated (O : Set E) (hO : IsOpen O)
    (u : E → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u O)
    (n : ℕ) (v : Fin n → E) (x : E) (hx : x ∈ O) :
    constantDirectionWord (List.ofFn v) u x = iteratedFDeriv ℝ n u x v := by
  induction n generalizing x with
  | zero => simp [constantDirectionWord, directionalWord]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hO.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have he : (fun y => constantDirectionWord (List.ofFn (Fin.tail v)) u y) =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ n u y (Fin.tail v)) :=
      Filter.Eventually.mono (hO.mem_nhds hx) (fun y hy => ih (Fin.tail v) y hy)
    simp only [List.ofFn_succ, constantDirectionWord, directionalWord]
    change fderiv ℝ (fun y => constantDirectionWord (List.ofFn (Fin.tail v)) u y) x (v 0) = _
    rw [he.fderiv_eq]

end FieldExpansion

section WordAlgebra
open RightFrame.PullbackWords
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem directional_map {A B : Type*} (fields : B → E → E)
    (f : A → B) (w : List A) (u : E → ℂ) :
    directionalWord fields (w.map f) u = directionalWord (fun a => fields (f a)) w u := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons, directionalWord, ih]

end WordAlgebra

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualWordSeminorm

end
