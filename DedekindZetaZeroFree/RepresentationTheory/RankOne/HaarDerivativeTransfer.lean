module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.CompactCharacterRightDerivatives

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.Casimir

open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator Topology

theorem compact_parameter_integral_hasDerivAt
    {K E : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure K) [IsFiniteMeasure μ]
    (F F' : ℝ → K → E)
    (hc : Continuous (fun p : ℝ × K => F p.1 p.2))
    (hc' : Continuous (fun p : ℝ × K => F' p.1 p.2))
    (hd : ∀ t k, HasDerivAt (fun s => F s k) (F' t k) t) (t : ℝ) :
    Integrable (F' t) μ ∧
      HasDerivAt (fun s => ∫ k, F s k ∂μ) (∫ k, F' t k ∂μ) t := by
  have hct (s : ℝ) : Continuous (F s) := hc.comp (continuous_const.prodMk continuous_id)
  have hc't (s : ℝ) : Continuous (F' s) := hc'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set K))).exists_bound_of_continuousOn hc'.continuousOn
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (t - 1) (t + 1)) (bound := fun _ => C)
  · exact Icc_mem_nhds (by linarith) (by linarith)
  · exact Eventually.of_forall fun s => (hct s).aestronglyMeasurable
  · exact (hct t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hc't t).aestronglyMeasurable
  · exact Eventually.of_forall fun k s hs => hC (s, k) ⟨hs, mem_univ k⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun k s _ => hd s k

noncomputable local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _

noncomputable def polySym (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  match n with
  | 0 => 1
  | 1 => Matrix.trace g
  | n + 2 => Matrix.trace g * polySym (n + 1) g - Matrix.det g * polySym n g
private theorem polySym_eq (n : ℕ) (g : RawU2) : polySym n g.val = rawSymmetricPowerTrace n g := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h h' => simp only [polySym, rawSymmetricPowerTrace, h, h']
private theorem entry_smooth (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ => g i j) :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff
private theorem trace_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace g) := by
  simp only [Matrix.trace, Fin.sum_univ_two]
  exact (entry_smooth 0 0).add (entry_smooth 1 1)
private theorem det_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun g : Matrix (Fin 2) (Fin 2) ℂ => Matrix.det g) := by
  simp only [Matrix.det_fin_two]
  exact ((entry_smooth 0 0).mul (entry_smooth 1 1)).sub
    ((entry_smooth 0 1).mul (entry_smooth 1 0))
private theorem polySym_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (polySym n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact contDiff_const
  | one => exact trace_smooth
  | more n h h' =>
    change ContDiff ℝ (⊤ : ℕ∞) (fun g => Matrix.trace g * polySym (n+1) g - Matrix.det g * polySym n g)
    apply ContDiff.sub
    · exact trace_smooth.mul h'
    · exact det_smooth.mul h
noncomputable def polyCharacter {d : ℕ} (ℓ : RawHarmonicType d) (g : Fin d → Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∏ j, polySym (2 * ℓ j) (g j) * star (Matrix.det (g j)) ^ ℓ j
private theorem polyCharacter_eq {d : ℕ} (ℓ : RawHarmonicType d) (g : Fin d → RawU2) :
    polyCharacter ℓ (fun j => (g j).val) = rawCharacter ℓ g := by
  apply Finset.prod_congr rfl
  intro j _
  rw [polySym_eq]
  change _ = _ / Matrix.det (g j).val ^ ℓ j
  have hd := Matrix.det_of_mem_unitary (g j).property
  have hid : star (Matrix.det (g j).val) = (Matrix.det (g j).val)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (Unitary.star_mul_self_of_mem hd)
  rw [hid, inv_pow, div_eq_mul_inv]
private theorem polyCharacter_smooth {d : ℕ} (ℓ : RawHarmonicType d) : ContDiff ℝ (⊤ : ℕ∞) (polyCharacter ℓ) := by
  apply contDiff_prod
  intro j _
  exact ((polySym_smooth _).comp (contDiff_apply ℝ _ j)).mul
    ((((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff).comp
      (det_smooth.comp (contDiff_apply ℝ _ j))).pow _)
noncomputable def matrixLift {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin d × Fin 3) (t : ℝ) :
    Fin d → Matrix (Fin 2) (Fin 2) ℂ :=
  fun j => if j = b.1 then NormedSpace.exp ((t : ℂ) • B b.1 b.2) else 1
private theorem matrixLift_smooth {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) (b : Fin d × Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (matrixLift B b) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hj : j = b.1
  · simp only [matrixLift, hj, if_true]
    have he : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) :=
      contDiff_iff_contDiffAt.mpr (fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt)
    exact he.comp ((Complex.ofRealCLM.contDiff).smul contDiff_const)
  · simp only [matrixLift, hj, if_false]
    exact contDiff_const
private theorem matrixLift_eq {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a) (b : Fin d × Fin 3) (t : ℝ) :
    matrixLift B b t = fun j => (basisLift B hskew b t j).val := by
  funext j
  by_cases hj : j = b.1 <;> simp [matrixLift, basisLift, basisExp, hj]
noncomputable def jetFunction {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3)
    (g : Fin d → Matrix (Fin 2) (Fin 2) ℂ) (t s : ℝ) : ℂ :=
  star (polyCharacter ℓ (g * matrixLift B b t * matrixLift B b s))
private theorem jetFunction_smooth {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ((Fin d → Matrix (Fin 2) (Fin 2) ℂ) × ℝ) × ℝ =>
      jetFunction B ℓ b p.1.1 p.1.2 p.2) := by
  apply Complex.conjCLE.contDiff.comp
  apply (polyCharacter_smooth ℓ).comp
  apply contDiff_pi.mpr
  intro j
  exact (((contDiff_apply ℝ _ j).comp (contDiff_fst.comp contDiff_fst)).mul
    (((contDiff_apply ℝ _ j).comp (matrixLift_smooth B b)).comp (contDiff_snd.comp contDiff_fst))).mul
    (((contDiff_apply ℝ _ j).comp (matrixLift_smooth B b)).comp contDiff_snd)
set_option maxHeartbeats 800000 in
private theorem firstJet_smooth {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin d → Matrix (Fin 2) (Fin 2) ℂ) × ℝ =>
      deriv (jetFunction B ℓ b p.1 p.2) 0) := by
  exact ((jetFunction_smooth B ℓ b).fderiv contDiff_const (by simp)).clm_apply contDiff_const
private theorem secondJet_smooth {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g : Fin d → Matrix (Fin 2) (Fin 2) ℂ =>
      deriv (fun t : ℝ => deriv (jetFunction B ℓ b g t) 0) 0) := by
  exact ((firstJet_smooth B ℓ b).fderiv contDiff_const (by simp)).clm_apply contDiff_const
set_option maxHeartbeats 800000 in

theorem characterSecondDerivative_continuous {d : ℕ}
    (B : Fin d → Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hskew : ∀ j a, star (B j a) = -B j a)
    (ℓ : RawHarmonicType d) (b : Fin d × Fin 3) :
    Continuous (characterSecondDerivative B hskew ℓ b) := by
  have hc := (secondJet_smooth B ℓ b).continuous.comp
    (show Continuous (fun g : Fin d → RawU2 => fun j => (g j).val) by fun_prop)
  have he (g : Fin d → RawU2) (t s : ℝ) :
      jetFunction B ℓ b (fun j => (g j).val) t s =
        star (rawCharacter ℓ (g * basisLift B hskew b t * basisLift B hskew b s)) := by
    unfold jetFunction
    rw [matrixLift_eq B hskew, matrixLift_eq B hskew]
    have hh : (((fun j => (g j).val) * fun j => (basisLift B hskew b t j).val) *
        fun j => (basisLift B hskew b s j).val) =
        (fun j => (g * basisLift B hskew b t * basisLift B hskew b s) j |>.val) := by
      funext j
      simp only [Pi.mul_apply, Submonoid.coe_mul]
    rw [hh]
    exact congrArg star (polyCharacter_eq ℓ _)
  change Continuous (fun g : Fin d → RawU2 =>
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      star (rawCharacter ℓ (g * basisLift B hskew b t * basisLift B hskew b s))) 0) 0)
  change Continuous (fun g : Fin d → RawU2 =>
    deriv (fun t : ℝ => deriv (fun s : ℝ => jetFunction B ℓ b (fun j => (g j).val) t s) 0) 0) at hc
  simpa only [he] using hc

end DedekindZetaZeroFree.RepresentationTheory.KPCompactHarmonicTruncation.Casimir
