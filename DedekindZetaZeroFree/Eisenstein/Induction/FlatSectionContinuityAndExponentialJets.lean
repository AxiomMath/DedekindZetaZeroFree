module

public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaCompactOverlap
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.Adeles.Approximation.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.Eisenstein.Induction.CompactAndFlatSections
public import DedekindZetaZeroFree.Eisenstein.Induction.Height.ChamberCosetBounds

@[expose] public section

section

noncomputable section
open scoped NumberField Classical Topology
namespace DedekindZetaZeroFree.KPLiteralChamber.JointProfile
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_flat_multiplier_formula
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (s : ℂ) (g : G F ζ hζ) :
    f.val s g = Complex.exp (s * (Real.log
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
        (literalIwasawa F ζ hζ K hK) g : NNReal) : ℝ)) : ℂ)) * f.val 0 g := by
  obtain ⟨t, x, k, rfl⟩ := hK.2.1 g
  have hnorm := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
    (literalIwasawa F ζ hζ K hK) t x k
  rw [hnorm]
  rw [KPLiteralExceptionalResidue.val_torus_root_compact, KPLiteralExceptionalResidue.val_torus_root_compact]
  exact f.property.2.1 s t k

theorem literal_log_modulus_continuous
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) :
    Continuous (fun g : G F ζ hζ => Real.log
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
        (literalIwasawa F ζ hζ K hK) g : NNReal) : ℝ))) := by
  have hnorm := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous
    F ζ hζ (literalIwasawa F ζ hζ K hK)
  exact hnorm.log (fun g => NNReal.coe_ne_zero.mpr (Units.ne_zero _))

end DedekindZetaZeroFree.KPLiteralChamber.JointProfile

end

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem chamberCoset_compact_covered_height_lower_bound
    (C : Set (G F ζ hζ)) (hC : IsCompact C) :
    ∃ m : ℝ, 0 < m ∧ ∀ c : KPChamberBruhatTwoCells.RationalQuotient F,
      ∀ g ∈ C, m * Projectivization.mulHeight (KPLiteralExceptionalResidue.chamberCosetIndex F c) ≤
        KPChamberHeight.height F (KPChamberHeight.bottomRow F (Quotient.out c))
          (KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ g) := by
  obtain ⟨m, M, hm, hmM, hb⟩ := KPChamberHeight.compact_uniform_height F
    ((KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ) '' C)
    (hC.image (KPLiteralExceptionalResidue.coveredHeightProjection_continuous F ζ hζ))
  obtain ⟨A, hA, hcompare⟩ := KPChamberHeight.height_one_compare F
  refine ⟨m, hm, fun c g hg => ?_⟩
  rw [KPLiteralExceptionalResidue.chamberCosetIndex_mulHeight_out]
  exact (mul_le_mul_of_nonneg_left (hcompare _).2.1 hm.le).trans
    (hb _ _ ⟨g, hg, rfl⟩).1

private theorem norm_flat_between_parameters (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (s s₀ s₁ : ℂ) (hlo : s₀.re ≤ s.re) (hhi : s.re ≤ s₁.re)
    (g : G F ζ hζ) :
    ‖f.val s g‖ ≤ ‖f.val s₀ g‖ + ‖f.val s₁ g‖ := by
  obtain ⟨t, x, k, rfl⟩ := hK.2.1 g
  simp only [KPLiteralExceptionalResidue.val_torus_root_compact,
    KPLiteralExceptionalResidue.norm_val_torus_compact]
  let d : ℝ := ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)
  have hd : 0 < d := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hprofile : 0 ≤ KPLiteralExceptionalResidue.normalizedTorusProfile F ζ hζ K f t k :=
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg hd.le _)
  by_cases hdone : 1 ≤ d
  · have he : d ^ (2 / 3 + s.re) ≤ d ^ (2 / 3 + s₁.re) :=
      Real.rpow_le_rpow_of_exponent_le hdone (by linarith)
    exact (mul_le_mul_of_nonneg_right he hprofile).trans
      (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hd.le _) hprofile))
  · have he : d ^ (2 / 3 + s.re) ≤ d ^ (2 / 3 + s₀.re) :=
      Real.rpow_le_rpow_of_exponent_ge hd (le_of_not_ge hdone) (by linarith)
    exact (mul_le_mul_of_nonneg_right he hprofile).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hd.le _) hprofile))

theorem chamber_scalar_compact_majorants (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (P : Set ℂ) (hP : IsCompact P)
    (hPc : P ⊆ {s : ℂ | (1 : ℝ) / 3 < s.re})
    (C : Set (G F ζ hζ)) (hC : IsCompact C) :
    ∃ b : KPChamberBruhatTwoCells.RationalQuotient F → ℝ,
      Summable b ∧ ∀ c s, s ∈ P → ∀ g, g ∈ C →
        ‖f.val s (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤ b c := by
  by_cases hne : P.Nonempty
  · obtain ⟨s₀, hs₀, hmin⟩ := hP.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨s₁, hs₁, hmax⟩ := hP.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨m, hm, hlow⟩ := chamberCoset_compact_covered_height_lower_bound F ζ hζ C hC
    have aux (z : ℂ) (hz : z ∈ P) :
        ∃ b : KPChamberBruhatTwoCells.RationalQuotient F → ℝ,
          Summable b ∧ ∀ c g, g ∈ C →
            ‖f.val z (rationalLift F ζ hζ (Quotient.out c) * g)‖ ≤ b c := by
      obtain ⟨B, hB, hb⟩ := KPLiteralExceptionalResidue.actualScalarHeightDecay F ζ hζ K hK f z (hPc hz)
      let a : ℝ := 2 / 3 + z.re
      have ha : 1 < a := by dsimp [a]; have := hPc hz; simp only [Set.mem_setOf_eq] at this; linarith
      let D : ℝ := B * m ^ (-2 * a)
      refine ⟨fun c => D * KPHeightSeries.term Projectivization.mulHeight a
        (KPLiteralExceptionalResidue.chamberCosetIndex F c),
        ((KPHeightSeries.relativeHeight_summable_tail F a ha).1.comp_injective
          (KPLiteralExceptionalResidue.chamberCosetIndex_injective F)).mul_left D, ?_⟩
      intro c g hg
      have he := hb (rationalLift F ζ hζ (Quotient.out c) * g)
      rw [KPLiteralExceptionalResidue.actualBaseRowHeight_rational_mul] at he
      have hpow :
          (KPChamberHeight.height F (KPChamberHeight.bottomRow F (Quotient.out c))
            (KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ g)) ^ (-2 * a) ≤
          (m * Projectivization.mulHeight (KPLiteralExceptionalResidue.chamberCosetIndex F c)) ^ (-2 * a) :=
        Real.rpow_le_rpow_of_nonpos
          (mul_pos hm (Projectivization.mulHeight_pos _)) (hlow c g hg) (by linarith)
      refine he.trans ((mul_le_mul_of_nonneg_left hpow hB).trans_eq ?_)
      rw [Real.mul_rpow hm.le (Projectivization.mulHeight_pos _).le]
      dsimp [D, KPHeightSeries.term]
      ring
    obtain ⟨b₀, hb₀, hbound₀⟩ := aux s₀ hs₀
    obtain ⟨b₁, hb₁, hbound₁⟩ := aux s₁ hs₁
    refine ⟨b₀ + b₁, hb₀.add hb₁, ?_⟩
    intro c s hs g hg
    exact (norm_flat_between_parameters F ζ hζ K hK f s s₀ s₁
      (hmin hs) (hmax hs) _).trans (add_le_add (hbound₀ c g hg) (hbound₁ c g hg))
  · refine ⟨0, summable_zero, ?_⟩
    intro c s hs g hg
    exact (hne ⟨s, hs⟩).elim

end DedekindZetaZeroFree.KPLiteralChamber

end

end

section

noncomputable section
open scoped ContDiff
namespace DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ExpJetPolynomial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem jet_succ (f : E → ℂ) (x : E) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (n : ℕ) (v : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x v =
      iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (v (Fin.last n))) x (Fin.init v) := by
  rw [iteratedFDeriv_succ_apply_right]
  let L : (E →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (v (Fin.last n))
  have hh := L.iteratedFDeriv_comp_left (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (i := n) (by simp)
  exact (congrArg (fun T => T (Fin.init v)) hh).symm

private theorem derivative_exp_mul (A B : E → ℂ) (x : E)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (s : ℂ) (w : E) :
    fderiv ℝ (fun y => Complex.exp (s * A y) * B y) x w =
      s * (Complex.exp (s * A x) * (fderiv ℝ A x w * B x)) +
        Complex.exp (s * A x) * fderiv ℝ B x w := by
  have hh := (((hA.hasFDerivAt.const_mul s).cexp).mul hB.hasFDerivAt).fderiv
  change fderiv ℝ ((fun y => Complex.exp (s * A y)) * B) x w = _
  rw [hh]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

theorem iteratedFDeriv_exp_mul_eq_exp_mul_polynomial
    (A B : E → ℂ) (x : E) (hA : ContDiffAt ℝ (⊤ : ℕ∞) A x)
    (hB : ContDiffAt ℝ (⊤ : ℕ∞) B x) (n : ℕ) (v : Fin n → E) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ s : ℂ,
      iteratedFDeriv ℝ n (fun y => Complex.exp (s * A y) * B y) x v =
        Complex.exp (s * A x) * P.eval s := by
  induction n generalizing B with
  | zero =>
    exact ⟨Polynomial.C (B x), by simp, by intro s; simp⟩
  | succ n ih =>
    let w := v (Fin.last n)
    let B₁ : E → ℂ := fun y => fderiv ℝ A y w * B y
    let B₂ : E → ℂ := fun y => fderiv ℝ B y w
    have h₁ : ContDiffAt ℝ (⊤ : ℕ∞) B₁ x :=
      ((hA.fderiv_right (by simp)).clm_apply contDiffAt_const).mul hB
    have h₂ : ContDiffAt ℝ (⊤ : ℕ∞) B₂ x :=
      (hB.fderiv_right (by simp)).clm_apply contDiffAt_const
    obtain ⟨P₁,hdeg₁,hP₁⟩ := ih B₁ h₁ (Fin.init v)
    obtain ⟨P₂,hdeg₂,hP₂⟩ := ih B₂ h₂ (Fin.init v)
    refine ⟨Polynomial.X * P₁ + P₂, ?_, ?_⟩
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_mul_le).trans (by
            rw [Polynomial.natDegree_X]
            omega)
      · exact hdeg₂.trans (Nat.le_succ n)
    · intro s
      have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Complex.exp (s * A y) * B y) x := by
        exact ((contDiffAt_const.mul hA).cexp).mul hB
      rw [jet_succ _ _ hs n v]
      have he : (fun y => fderiv ℝ (fun z => Complex.exp (s * A z) * B z) y w) =ᶠ[nhds x]
          (fun y => s * (Complex.exp (s * A y) * B₁ y) + Complex.exp (s * A y) * B₂ y) := by
        have hA1 : ContDiffAt ℝ 1 A x := hA.of_le (by simp)
        have hB1 : ContDiffAt ℝ 1 B x := hB.of_le (by simp)
        have ha : ∀ᶠ y in nhds x, DifferentiableAt ℝ A y :=
          (hA1.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by simp))
        have hb : ∀ᶠ y in nhds x, DifferentiableAt ℝ B y :=
          (hB1.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by simp))
        filter_upwards [ha,hb] with y hyA hyB
        exact derivative_exp_mul A B y hyA hyB s w
      rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
      have hs₁ : ContDiffAt ℝ n (fun y => Complex.exp (s * A y) * B₁ y) x :=
        (((contDiffAt_const.mul hA).cexp).mul h₁).of_le (by simp)
      have hs₂ : ContDiffAt ℝ n (fun y => Complex.exp (s * A y) * B₂ y) x :=
        (((contDiffAt_const.mul hA).cexp).mul h₂).of_le (by simp)
      have hsm : ContDiffAt ℝ n (s • (fun y => Complex.exp (s * A y) * B₁ y)) x := hs₁.const_smul s
      have hadd := iteratedFDeriv_add_apply hsm hs₂
      have hsmul := iteratedFDeriv_const_smul_apply (a := s) hs₁
      change iteratedFDeriv ℝ n ((s • (fun y => Complex.exp (s * A y) * B₁ y)) +
        (fun y => Complex.exp (s * A y) * B₂ y)) x (Fin.init v) = _
      rw [hadd, ContinuousMultilinearMap.add_apply, hsmul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul, hP₁ s, hP₂ s]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      ring

end DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ExpJetPolynomial

end
end

section

noncomputable section
open scoped NumberField Classical Topology
namespace DedekindZetaZeroFree.KPLiteralChamber.JointProfile
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup P] [NormedSpace ℝ P]
private theorem partial_smooth (H : P × E → ℂ) (U : Set P) (V : Set E)
    (hU : IsOpen U) (hV : IsOpen V) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (U ×ˢ V))
    (n : ℕ) (v : Fin n → E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : P × E => iteratedFDeriv ℝ n (fun x => H (p.1,x)) p.2 v) (U ×ˢ V) := by
  induction n with
  | zero => simpa using hH
  | succ n ih =>
    intro p hp
    let Q := fun q : P × E => iteratedFDeriv ℝ n (fun x => H (q.1,x)) q.2 (Fin.tail v)
    have hQ : ContDiffAt ℝ (⊤ : ℕ∞) Q p := (ih (Fin.tail v)).contDiffAt ((hU.prod hV).mem_nhds hp)
    have hQQ : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun q : (P × E) × E => Q (q.1.1,q.2)) (p,p.2) :=
      by
        simpa only [Function.comp_def] using hQ.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hD : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : P × E => fderiv ℝ (fun x => Q (q.1,x)) q.2) p := by
      exact hQQ.fderiv contDiffAt_snd (by simp)
    have hA := hD.clm_apply (contDiffAt_const (c := v 0))
    apply hA.contDiffWithinAt.congr_of_eventuallyEq_insert
    have hn : ∀ᶠ q in nhds p, q ∈ U ×ˢ V := (hU.prod hV).mem_nhds hp
    have he : ∀ᶠ q in nhds p,
        fderiv ℝ (fun x => Q (q.1,x)) q.2 (v 0) =
          iteratedFDeriv ℝ (n+1) (fun x => H (q.1,x)) q.2 v := by
      filter_upwards [hn] with q hq
      have hh : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => H (q.1,x)) q.2 :=
        (hH.contDiffAt ((hU.prod hV).mem_nhds hq)).comp q.2
          (contDiffAt_const.prodMk contDiffAt_id)
      have ht : DifferentiableAt ℝ (iteratedFDeriv ℝ n (fun x => H (q.1,x))) q.2 :=
        (hh.iteratedFDeriv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
      exact ht.iteratedFDeriv_succ_apply_left'.symm
    exact (he.mono (fun q hq => hq.symm)).filter_mono nhdsWithin_le_nhds
open KPGlobalResidualConstruction KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
private def jet (n : ℕ) (v : Fin n → ArchCoordinates F) (u : KPLiteralRaw.G F ζ hζ → ℂ) (g : KPLiteralRaw.G F ζ hζ) :=
  iteratedFDeriv ℝ n (fun x => u (g * archChart F ζ hζ x)) (archBase F) v
private def μ (p : ArchCoordinates F × ArchCoordinates F) : ArchCoordinates F := fun q =>
  ![p.1 q 0 + p.1 q 1 * p.2 q 0 / (1 + p.1 q 2 * p.2 q 0),
    p.1 q 1 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)^2,
    p.2 q 2 + p.1 q 2 * p.2 q 1 / (1 + p.1 q 2 * p.2 q 0)]
set_option maxHeartbeats 800000 in
private theorem jet_continuous (n : ℕ) (v : Fin n → ArchCoordinates F)
    (u : KPLiteralRaw.G F ζ hζ → ℂ) (hu : Smooth F ζ hζ u) : Continuous (jet F ζ hζ n v u) := by
  obtain ⟨V,hVo,hb,hVD,hμ,hμD,hprod,hthick,hcomm⟩ :=
    KPLiteralChamber.JointProfile.ArchChartProduct.actual_archChart_product F ζ hζ
  change ContDiffOn ℝ (⊤ : ℕ∞) (μ F) (V ×ˢ V) at hμ
  change Set.MapsTo (μ F) (V ×ˢ V) (archDomain F) at hμD
  change ∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (μ F (y,x)) = archChart F ζ hζ y * archChart F ζ hζ x at hprod
  obtain ⟨U,hU⟩ := hu.2.2
  apply continuous_iff_continuousAt.mpr
  intro g
  let H := fun p : ArchCoordinates F × ArchCoordinates F => u (g * archChart F ζ hζ (μ F p))
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ V) := (hu.2.1 g).comp hμ hμD
  have hj : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p => iteratedFDeriv ℝ n (fun x => H (p.1,x)) p.2 v) (archBase F,archBase F) :=
    (partial_smooth H V V hVo hVo hH n v).contDiffAt ((hVo.prod hVo).mem_nhds ⟨hb,hb⟩)
  let J := fun y => iteratedFDeriv ℝ n (fun x => H (y,x)) (archBase F) v
  have hJ : ContinuousAt J (archBase F) := by
    have hc := ContinuousAt.comp (f := fun y : ArchCoordinates F => (y,archBase F)) (x := archBase F) hj.continuousAt (continuousAt_id.prodMk continuousAt_const)
    simpa only [Function.comp_def] using hc
  have heq (y : ArchCoordinates F) (hy : y ∈ V)
      (a : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) :
      jet F ζ hζ n v u (g * (archChart F ζ hζ y * a.val)) = J y := by
    have he : (fun x => u ((g * (archChart F ζ hζ y * a.val)) * archChart F ζ hζ x)) =ᶠ[nhds (archBase F)]
        (fun x => H (y,x)) := by
      filter_upwards [show ∀ᶠ x in nhds (archBase F), x ∈ V from hVo.mem_nhds hb] with x hx
      dsimp [H]
      rw [hprod y hy x hx]
      rw [mul_assoc g, mul_assoc (archChart F ζ hζ y), (hcomm U a.val a.property x).eq.symm,
        ← mul_assoc, ← mul_assoc, hU _ a.val a.property, mul_assoc]
    exact congrArg (fun T => T v) ((he.iteratedFDeriv ℝ n).self_of_nhds)
  have hbase : J (archBase F) = jet F ζ hζ n v u g := by
    simpa only [KPInterface.ResidueConstruction.Raw.archChart_base, Subgroup.coe_one, mul_one] using
      (heq (archBase F) hb 1).symm
  apply Filter.tendsto_def.mpr
  intro S hS
  have hn : J ⁻¹' S ∈ nhds (archBase F) := hJ (by rwa [hbase])
  obtain ⟨W,hW,hoW,hbW⟩ := mem_nhds_iff.mp (Filter.inter_mem hn (hVo.mem_nhds hb))
  have hWV : W ⊆ V := fun y hy => (hW hy).2
  have hT := hthick W hoW hbW hWV U
  have hG : (fun k : KPLiteralRaw.G F ζ hζ => g⁻¹ * k) ⁻¹'
      {k | ∃ y ∈ W, ∃ a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        k = archChart F ζ hζ y * a} ∈ nhds g := by
    have hc : ContinuousAt (fun k : KPLiteralRaw.G F ζ hζ => g⁻¹ * k) g := continuousAt_const.mul continuousAt_id
    exact hc (by simpa using hT)
  apply Filter.mem_of_superset hG
  intro k hk
  obtain ⟨y,hy,a,ha,hk⟩ := hk
  have hk' : k = g * (archChart F ζ hζ y * a) := by rw [← hk]; group
  change jet F ζ hζ n v u k ∈ S
  rw [hk', heq y (hWV hy) ⟨a,ha⟩]
  exact (hW hy).1
private def logM (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (g : KPLiteralRaw.G F ζ hζ) : ℝ := Real.log
  (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) g : NNReal) : ℝ))
private theorem logM_chart_smooth
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (g : KPLiteralRaw.G F ζ hζ) (hg : f.val 0 g ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (logM F ζ hζ K hK (g * archChart F ζ hζ x) : ℂ)) (archBase F) := by
  have hD : IsOpen (archDomain F) := by
    change IsOpen {x : ArchCoordinates F | ∀ w, x w 1 ≠ 0}
    have he : {x : ArchCoordinates F | ∀ w, x w 1 ≠ 0} = ⋂ w, {x | x w 1 ≠ 0} := by ext; simp
    rw [he]; exact isOpen_iInter_of_finite (fun w => isOpen_ne_fun (by fun_prop) continuous_const)
  have hb : archBase F ∈ archDomain F := by intro w; simp [archBase]
  have hh (s : ℂ) : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => f.val s (g * archChart F ζ hζ x)) (archBase F) :=
    ((f.property.1 s).1.2.1 g).contDiffAt (hD.mem_nhds hb)
  have h0 : f.val 0 (g * archChart F ζ hζ (archBase F)) ≠ 0 := by
    simpa [KPInterface.ResidueConstruction.Raw.archChart_base] using hg
  have h1 : f.val 1 (g * archChart F ζ hζ (archBase F)) ≠ 0 := by
    rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f]
    exact mul_ne_zero (Complex.exp_ne_zero _) h0
  have hs := (((hh 1).norm ℂ h1).log (norm_ne_zero_iff.mpr h1)).sub
    (((hh 0).norm ℂ h0).log (norm_ne_zero_iff.mpr h0))
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp (archBase F) hs
  have he : (fun x => (Real.log ‖f.val 1 (g * archChart F ζ hζ x)‖ -
      Real.log ‖f.val 0 (g * archChart F ζ hζ x)‖ : ℂ)) =ᶠ[nhds (archBase F)]
        (fun x => (logM F ζ hζ K hK (g * archChart F ζ hζ x) : ℂ)) := by
    filter_upwards [(hh 0).continuousAt.eventually_ne h0] with x hx
    rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f]
    simp only [one_mul, norm_mul, Complex.norm_exp, Complex.ofReal_re]
    rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hx), Real.log_exp]
    simp [logM]
  apply hc.congr_of_eventuallyEq
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_sub] using he.symm
private def node (n : ℕ) (i : Fin (n+1)) : ℂ := (i.val : ℂ)
private def basisEval (n : ℕ) (i : Fin (n+1)) (s : ℂ) : ℂ :=
  (Lagrange.basis Finset.univ (node n) i).eval s
private theorem polynomial_nodes (n : ℕ) (P : Polynomial ℂ) (hP : P.natDegree ≤ n) (s : ℂ) :
    P.eval s = ∑ i : Fin (n+1), P.eval (node n i) * basisEval n i s := by
  have hi : Function.Injective (node n) := by
    intro i j h
    apply Fin.ext
    dsimp [node] at h
    exact_mod_cast h
  have hd : P.degree < (Finset.univ : Finset (Fin (n+1))).card :=
    Polynomial.degree_le_natDegree.trans_lt (by simpa using (show (P.natDegree : WithBot ℕ) < (n+1 : ℕ) by exact_mod_cast Nat.lt_succ_of_le hP))
  nth_rw 1 [Lagrange.eq_interpolate hi.injOn hd]
  simp [Lagrange.interpolate_apply, basisEval, Polynomial.eval_finsetSum]
private theorem jet_poly_at_nonzero
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (v : Fin n → ArchCoordinates F)
    (g : KPLiteralRaw.G F ζ hζ) (hg : f.val 0 g ≠ 0) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ s : ℂ,
      jet F ζ hζ n v (f.val s) g = Complex.exp (s * (logM F ζ hζ K hK g : ℂ)) * P.eval s := by
  have hD : IsOpen (archDomain F) := by
    change IsOpen {x : ArchCoordinates F | ∀ w, x w 1 ≠ 0}
    have he : {x : ArchCoordinates F | ∀ w, x w 1 ≠ 0} = ⋂ w, {x | x w 1 ≠ 0} := by ext; simp
    rw [he]; exact isOpen_iInter_of_finite (fun w => isOpen_ne_fun (by fun_prop) continuous_const)
  have hb : archBase F ∈ archDomain F := by intro w; simp [archBase]
  obtain ⟨P,hP,he⟩ := KPLiteralChamber.JointProfile.ExpJetPolynomial.iteratedFDeriv_exp_mul_eq_exp_mul_polynomial
    (fun x => (logM F ζ hζ K hK (g * archChart F ζ hζ x) : ℂ))
    (fun x => f.val 0 (g * archChart F ζ hζ x)) (archBase F)
    (logM_chart_smooth F ζ hζ K hK f g hg)
    (((f.property.1 0).1.2.1 g).contDiffAt (hD.mem_nhds hb)) n v
  refine ⟨P,hP,?_⟩
  intro s
  have hfun : (fun x => Complex.exp (s * (logM F ζ hζ K hK (g * archChart F ζ hζ x) : ℂ)) *
      f.val 0 (g * archChart F ζ hζ x)) = (fun x => f.val s (g * archChart F ζ hζ x)) := by
    funext x; exact (KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f s _).symm
  simpa only [hfun, KPInterface.ResidueConstruction.Raw.archChart_base, mul_one, jet] using he s

private theorem units_cont {R X : Type*} [NormedRing R] [HasSummableGeomSeries R]
    [TopologicalSpace X] (f : X → Rˣ) (x : X) (hf : ContinuousAt (fun y => (f y : R)) x) :
    ContinuousAt f x := by
  exact (Units.isOpenEmbedding_val.isEmbedding.isInducing.continuousAt_iff).mpr hf
private theorem matrix_cont (w : NumberField.InfinitePlace F) (x : ArchCoordinates F) (hx : x w 1 ≠ 0) :
    ContinuousAt (fun y : ArchCoordinates F => KPLiteralChamber.rightMatrix (y w)) x := by
  have he : (fun y : ArchCoordinates F => (KPLiteralChamber.rightMatrix (y w)).val) =ᶠ[nhds x]
      (fun y => !![y w 1 + y w 0 * y w 2, y w 0; y w 2, 1]) := by
    have hc : ContinuousAt (fun y : ArchCoordinates F => y w 1) x :=
      ((continuous_apply 1).comp (continuous_apply w)).continuousAt
    filter_upwards [hc.eventually_ne hx] with y hy
    exact KPLiteralChamber.rightMatrix_val (y w) hy
  have hc : ContinuousAt (fun y : ArchCoordinates F => (KPLiteralChamber.rightMatrix (y w)).val) x := by
    have ev (k : Fin 3) : ContinuousAt (fun y : ArchCoordinates F => y w k) x :=
      ((continuous_apply k).comp (continuous_apply w)).continuousAt
    apply ContinuousAt.congr_of_eventuallyEq _ he
    apply continuousAt_pi.mpr; intro i
    apply continuousAt_pi.mpr; intro j
    fin_cases i <;> fin_cases j <;> simp
    · exact (ev 1).add ((ev 0).mul (ev 2))
    · exact ((continuous_apply 0).comp (continuous_apply w)).continuousAt
    · exact ((continuous_apply 2).comp (continuous_apply w)).continuousAt
    · exact continuousAt_const
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  have hh := units_cont (fun y : ArchCoordinates F => KPLiteralChamber.rightMatrix (y w)) x hc
  simpa using! hh
private theorem chart_cont (x : ArchCoordinates F) (hx : x ∈ archDomain F) :
    ContinuousAt (archChart F ζ hζ) x := by
  have hmat : ContinuousAt (fun y : ArchCoordinates F => fun w =>
      Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (y w))) x := by
    apply continuousAt_pi.mpr; intro w
    exact ContinuousAt.comp (f := fun y : ArchCoordinates F => KPLiteralChamber.rightMatrix (y w))
      QuotientGroup.continuous_mk.continuousAt (matrix_cont F w x (hx w))
  have hh := ContinuousAt.comp (f := fun y : ArchCoordinates F => fun w =>
      Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (y w)))
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.continuousAt hmat
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => KPLiteralChamber.right_insertion F ζ hζ y)

private def normalizedJet
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (v : Fin n → ArchCoordinates F) (s : ℂ)
    (g : KPLiteralRaw.G F ζ hζ) : ℂ :=
  Complex.exp (-s * (logM F ζ hζ K hK g : ℂ)) * jet F ζ hζ n v (f.val s) g

private theorem normalizedJet_continuous
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (v : Fin n → ArchCoordinates F) (s : ℂ) :
    Continuous (normalizedJet F ζ hζ K hK f n v s) := by
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (literal_log_modulus_continuous F ζ hζ K hK))).cexp.mul
      (jet_continuous F ζ hζ n v (f.val s) (f.property.1 s).1)

private theorem jet_zero_on_interior
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (v : Fin n → ArchCoordinates F) (s : ℂ)
    (g : KPLiteralRaw.G F ζ hζ) (hg : g ∈ interior {h | f.val 0 h = 0}) :
    jet F ζ hζ n v (f.val s) g = 0 := by
  have hb : archBase F ∈ archDomain F := by intro w; simp [archBase]
  have hc : ContinuousAt (fun x => g * archChart F ζ hζ x) (archBase F) :=
    continuousAt_const.mul (chart_cont F ζ hζ (archBase F) hb)
  have hz : ∀ᶠ x in nhds (archBase F), f.val 0 (g * archChart F ζ hζ x) = 0 := by
    have hh := hc (by simpa only [KPInterface.ResidueConstruction.Raw.archChart_base,
      mul_one] using (show {h | f.val 0 h = 0} ∈ nhds g from mem_interior_iff_mem_nhds.mp hg))
    exact hh
  have he : (fun x => f.val s (g * archChart F ζ hζ x)) =ᶠ[nhds (archBase F)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hz] with x hx
    rw [literal_flat_multiplier_formula F ζ hζ K hK f, hx, mul_zero]
  change iteratedFDeriv ℝ n _ _ v = _
  rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
  simp

private theorem normalizedJet_interpolation
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (n : ℕ) (v : Fin n → ArchCoordinates F) (s : ℂ)
    (g : KPLiteralRaw.G F ζ hζ) :
    normalizedJet F ζ hζ K hK f n v s g =
      ∑ i : Fin (n+1), normalizedJet F ζ hζ K hK f n v (node n i) g * basisEval n i s := by
  let N : Set (KPLiteralRaw.G F ζ hζ) := {h | f.val 0 h ≠ 0}
  have hd : Dense (N ∪ interior Nᶜ) := by
    intro h
    by_cases hh : h ∈ closure N
    · exact closure_mono Set.subset_union_left hh
    · apply subset_closure
      right
      simpa only [interior_eq_compl_closure_compl, compl_compl, Set.mem_compl_iff] using hh
  have he : Set.EqOn (normalizedJet F ζ hζ K hK f n v s)
      (fun h => ∑ i : Fin (n+1), normalizedJet F ζ hζ K hK f n v (node n i) h * basisEval n i s)
      (N ∪ interior Nᶜ) := by
    intro h hh
    rcases hh with hh | hh
    · obtain ⟨P,hP,hpoly⟩ := jet_poly_at_nonzero F ζ hζ K hK f n v h hh
      have hn (z : ℂ) : normalizedJet F ζ hζ K hK f n v z h = P.eval z := by
        dsimp [normalizedJet]
        rw [hpoly z, ← mul_assoc, ← Complex.exp_add]
        simp
      simp_rw [hn]
      exact polynomial_nodes n P hP s
    · have hz (z : ℂ) : normalizedJet F ζ hζ K hK f n v z h = 0 := by
        dsimp [normalizedJet]
        rw [jet_zero_on_interior F ζ hζ K hK f n v z h (by
          simpa only [N, Set.compl_setOf, not_not] using hh), mul_zero]
      simp [hz]
  have hc : Continuous (fun h => ∑ i : Fin (n+1),
      normalizedJet F ζ hζ K hK f n v (node n i) h * basisEval n i s) := by
    exact continuous_finsetSum _ (fun i _ =>
      (normalizedJet_continuous F ζ hζ K hK f n v (node n i)).mul_const _)
  exact he.closure (normalizedJet_continuous F ζ hζ K hK f n v s) hc (hd g)

theorem literal_multiplier_spatial_jet_continuous
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (j : KPGlobalResidualConstruction.Jet F) :
    Continuous (fun p : ℂ × KPLiteralRaw.G F ζ hζ =>
      iteratedFDeriv ℝ j.1
        (fun x => Complex.exp (p.1 * (Real.log
          (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
            (literalIwasawa F ζ hζ K hK)
            (p.2 * KPGlobalResidualConstruction.archChart F ζ hζ x) : NNReal) : ℝ)) : ℂ)) *
          f.val 0 (p.2 * KPGlobalResidualConstruction.archChart F ζ hζ x))
        (KPGlobalResidualConstruction.archBase F) j.2) := by
  rcases j with ⟨n,v⟩
  have hfun : (fun p : ℂ × KPLiteralRaw.G F ζ hζ =>
      iteratedFDeriv ℝ n
        (fun x => Complex.exp (p.1 * (logM F ζ hζ K hK (p.2 * archChart F ζ hζ x) : ℂ)) *
          f.val 0 (p.2 * archChart F ζ hζ x)) (archBase F) v) =
      (fun p => jet F ζ hζ n v (f.val p.1) p.2) := by
    funext p
    have he : (fun x => Complex.exp (p.1 * (logM F ζ hζ K hK (p.2 * archChart F ζ hζ x) : ℂ)) *
        f.val 0 (p.2 * archChart F ζ hζ x)) = (fun x => f.val p.1 (p.2 * archChart F ζ hζ x)) := by
      funext x
      exact (literal_flat_multiplier_formula F ζ hζ K hK f p.1 _).symm
    rw [he]
    rfl
  change Continuous (fun p : ℂ × KPLiteralRaw.G F ζ hζ =>
    iteratedFDeriv ℝ n
      (fun x => Complex.exp (p.1 * (logM F ζ hζ K hK (p.2 * archChart F ζ hζ x) : ℂ)) *
        f.val 0 (p.2 * archChart F ζ hζ x)) (archBase F) v)
  rw [hfun]
  have hinterp : (fun p : ℂ × KPLiteralRaw.G F ζ hζ => jet F ζ hζ n v (f.val p.1) p.2) =
      (fun p => Complex.exp (p.1 * (logM F ζ hζ K hK p.2 : ℂ)) *
        ∑ i : Fin (n+1), normalizedJet F ζ hζ K hK f n v (node n i) p.2 * basisEval n i p.1) := by
    funext p
    rw [← normalizedJet_interpolation F ζ hζ K hK f n v p.1 p.2]
    dsimp [normalizedJet]
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  rw [hinterp]
  have hc : Continuous (fun p : ℂ × KPLiteralRaw.G F ζ hζ =>
      Complex.exp (p.1 * (logM F ζ hζ K hK p.2 : ℂ))) :=
    (continuous_fst.mul (Complex.continuous_ofReal.comp
      ((literal_log_modulus_continuous F ζ hζ K hK).comp continuous_snd))).cexp
  apply hc.mul
  exact continuous_finsetSum _ (fun i _ =>
    ((normalizedJet_continuous F ζ hζ K hK f n v (node n i)).comp continuous_snd).mul
      ((Lagrange.basis Finset.univ (node n) i).continuous.comp continuous_fst))

end DedekindZetaZeroFree.KPLiteralChamber.JointProfile

end
end
section

noncomputable section
open scoped NumberField Classical Topology
namespace DedekindZetaZeroFree.KPLiteralChamber.JointProfile
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_normalized_jet_profile_continuous
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (P : Set ℂ) (hP : IsCompact P)
    (j : KPGlobalResidualConstruction.Jet F) :
    Continuous (fun p : KPGlobalTorusFunctionData.E F ζ hζ × (K × P) =>
      ‖iteratedFDeriv ℝ j.1
        (fun x => f.val p.2.2.val
          ((p.1.val * p.2.1.val) * KPGlobalResidualConstruction.archChart F ζ hζ x))
        (KPGlobalResidualConstruction.archBase F) j.2‖ /
        (((KPGlobalTorusFunctionData.delta F ζ hζ p.1 : NNReal) : ℝ)) ^
          ((2 : ℝ) / 3 + p.2.2.val.re)) := by
  have hj : Continuous (fun p : ℂ × G F ζ hζ =>
      iteratedFDeriv ℝ j.1
        (fun x => f.val p.1 (p.2 * KPGlobalResidualConstruction.archChart F ζ hζ x))
        (KPGlobalResidualConstruction.archBase F) j.2) := by
    convert literal_multiplier_spatial_jet_continuous F ζ hζ K hK f j using 1
    funext p
    congr 2
    funext x
    exact literal_flat_multiplier_formula F ζ hζ K hK f p.1 _
  have hd : Continuous (fun t : KPGlobalTorusFunctionData.E F ζ hζ =>
      ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
    have hn : Continuous (fun t : KPGlobalTorusFunctionData.E F ζ hζ =>
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ t : NNReal) : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp
        (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
    have he : (fun t : KPGlobalTorusFunctionData.E F ζ hζ =>
        ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) =
        (fun t => ((KPGlobalCenterRationalCharacter.nu F ζ hζ t : NNReal) : ℝ) ^
          (6 : ℝ)) := by
      funext t
      rw [KPGlobalCenterRationalCharacter.nu_formula]
      change _ = (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ) ^
        ((1 : ℝ) / 6)) ^ (6 : ℝ)
      rw [← Real.rpow_mul (NNReal.coe_nonneg _)]
      norm_num
    rw [he]
    exact hn.rpow_const (fun t => Or.inl (ne_of_gt
      (KPGlobalCenterRationalCharacter.nu_positive F ζ hζ t)))
  have hdpos (t : KPGlobalTorusFunctionData.E F ζ hζ) :
      0 < ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  apply Continuous.div
  · apply Continuous.norm
    exact hj.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).prodMk
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))
  · exact (hd.comp continuous_fst).rpow
      (continuous_const.add (Complex.continuous_re.comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
      (fun p => Or.inl (ne_of_gt (hdpos p.1)))
  · intro p
    exact ne_of_gt (Real.rpow_pos_of_pos (hdpos p.1) _)

end DedekindZetaZeroFree.KPLiteralChamber.JointProfile

end
end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rightJet (j : KPGlobalResidualConstruction.Jet F)
    (v : Functions F ζ hζ) (g : G F ζ hζ) : ℂ :=
  iteratedFDeriv ℝ j.1
    (fun x => v (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
    (KPGlobalResidualConstruction.archBase F) j.2

private theorem jet_chart_smooth (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (g : G F ζ hζ) (n : ℕ) :
    ContDiffAt ℝ n
      (fun x => f.val s (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archBase F) := by
  have hopen : IsOpen (KPGlobalResidualConstruction.archDomain F) := by
    change IsOpen {x : KPGlobalResidualConstruction.ArchCoordinates F | ∀ w, x w 1 ≠ 0}
    have he : {x : KPGlobalResidualConstruction.ArchCoordinates F | ∀ w, x w 1 ≠ 0} =
        ⋂ w, {x | x w 1 ≠ 0} := by ext x; simp
    rw [he]
    exact isOpen_iInter_of_finite (fun w => isOpen_ne.preimage
      ((continuous_apply 1).comp (continuous_apply w)))
  have hmem : KPGlobalResidualConstruction.archBase F ∈
      KPGlobalResidualConstruction.archDomain F := by
    intro w
    simp [KPGlobalResidualConstruction.archBase]
  exact (((f.property.1 s).1.2.1 g).contDiffAt (hopen.mem_nhds hmem)).of_le
    (by exact_mod_cast le_top)

theorem rightJet_compactExtension_rational_eq
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (s : ℂ) (j : KPGlobalResidualConstruction.Jet F)
    (a : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ) :
    rightJet F ζ hζ j
      (fun h => compactExtension F ζ hζ K hK (f.val 0) s
        (rationalLift F ζ hζ a * h)) g =
      rightJet F ζ hζ j (f.val s) (rationalLift F ζ hζ a * g) := by
  have he : (fun x => compactExtension F ζ hζ K hK (f.val 0) s
      (rationalLift F ζ hζ a * (g * KPGlobalResidualConstruction.archChart F ζ hζ x))) =
      (fun x => f.val s ((rationalLift F ζ hζ a * g) *
        KPGlobalResidualConstruction.archChart F ζ hζ x)) := by
    funext x
    rw [compactExtension_eq_flat, mul_assoc]
  unfold rightJet
  rw [he]

theorem rightJet_induction_covariance (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (j : KPGlobalResidualConstruction.Jet F)
    (r : R F ζ hζ) (u : KPAdeles F) (g : G F ζ hζ) :
    rightJet F ζ hζ j (f.val s)
      ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ u) * g) =
    (KPGlobalExceptionalParameter.realLogPower
      (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2 + s) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ)) *
      rightJet F ζ hζ j (f.val s) g := by
  let a : ℂ := KPGlobalExceptionalParameter.realLogPower
      (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2 + s) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ)
  have he : (fun x => f.val s (((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ u) * g) *
      KPGlobalResidualConstruction.archChart F ζ hζ x)) =
      (fun x => a • f.val s (g * KPGlobalResidualConstruction.archChart F ζ hζ x)) := by
    funext x
    rw [mul_assoc, (f.property.1 s).2 r u]
    rfl
  unfold rightJet
  rw [he, iteratedFDeriv_const_smul_apply' (jet_chart_smooth F ζ hζ K f s g j.1)]
  rfl

theorem norm_rightJet_induction_covariance (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (j : KPGlobalResidualConstruction.Jet F)
    (r : R F ζ hζ) (u : KPAdeles F) (g : G F ζ hζ) :
    ‖rightJet F ζ hζ j (f.val s)
      ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ u) * g)‖ =
    (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) ^
      ((2 : ℝ) / 3 + s.re) * ‖rightJet F ζ hζ j (f.val s) g‖ := by
  have hd : (0 : ℝ) < ((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
      (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ r.val)))
  rw [rightJet_induction_covariance F ζ hζ K f s j r u g, norm_mul, norm_mul,
    KPLiteralExceptionalResidue.norm_realLogPower _ hd _, KPLiteralExceptionalResidue.lambdaR_norm_eq F ζ hζ r,
    ← Real.rpow_add hd]
  congr 2
  rw [Complex.add_re]
  norm_num
  ring

theorem rightJet_N_invariant (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (j : KPGlobalResidualConstruction.Jet F)
    (x : KPAdeles F) (g : G F ζ hζ) :
    rightJet F ζ hζ j (f.val s) (KPGlobalTorusFunctionData.N F ζ hζ x * g) =
      rightJet F ζ hζ j (f.val s) g := by
  have h := rightJet_induction_covariance F ζ hζ K f s j
    (1 : R F ζ hζ) x g
  simpa [KPGlobalExceptionalParameter.realLogPower] using h

theorem rightJet_torus_root (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (j : KPGlobalResidualConstruction.Jet F)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    rightJet F ζ hζ j (f.val s) ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      rightJet F ζ hζ j (f.val s) (t.val * g) := by
  rw [coveredTorus_normalizes_upperRoot F ζ hζ t x, mul_assoc,
    rightJet_N_invariant]

theorem normalized_rightJet_R_invariant (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (j : KPGlobalResidualConstruction.Jet F)
    (r : R F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ) (g : G F ζ hζ) :
    ‖rightJet F ζ hζ j (f.val s) ((r.val * t).val * g)‖ /
        (((KPGlobalTorusFunctionData.delta F ζ hζ (r.val * t) : NNReal) : ℝ)) ^
          ((2 : ℝ) / 3 + s.re) =
      ‖rightJet F ζ hζ j (f.val s) (t.val * g)‖ /
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^
          ((2 : ℝ) / 3 + s.re) := by
  have hd (a : KPGlobalTorusFunctionData.E F ζ hζ) :
      (0 : ℝ) < ((KPGlobalTorusFunctionData.delta F ζ hζ a : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
      (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ a)))
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have h := norm_rightJet_induction_covariance F ζ hζ K f s j r 0 (t.val * g)
  simp only [hN, mul_one] at h
  rw [Subgroup.coe_mul, mul_assoc, h, map_mul, Units.val_mul, NNReal.coe_mul,
    Real.mul_rpow (hd r.val).le (hd t).le]
  exact mul_div_mul_left _ _ (ne_of_gt (Real.rpow_pos_of_pos (hd r.val) _))

theorem rightJet_zero (v : Functions F ζ hζ) (g : G F ζ hζ)
    (m : Fin 0 → KPGlobalResidualConstruction.ArchCoordinates F) :
    rightJet F ζ hζ ⟨0, m⟩ v g = v g := by
  simp [rightJet, iteratedFDeriv_zero_apply,
    KPInterface.ResidueConstruction.Raw.archChart_base]

private theorem jet_upper_projection (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (x : KPAdeles F) :
    ∃ B : KPChamberHeight.AdelGL F, B 1 0 = 0 ∧
      Matrix.ProjGenLinGroup.mk B = KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
  have hroot : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPGlobalTorusFunctionData.N F ζ hζ x) =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
        (Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x) := by
    change QuotientGroup.mk' _
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ (KPRationalAdelicSplitting.N F ζ hζ x)) = _
    congr 1
    have ht (v : KPHilbert.Place F) :
        KPAdelicCoverRestrictedProduct.matrixEval F v
          (Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x) =
        KubotaRankTwo.n (KPHilbert.Completion F v) (KPAdelicCoverRestrictedProduct.adeleEval F v x) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [KPAdelicCoverRestrictedProduct.matrixEval, Matrix.GeneralLinearGroup.transvection,
          Matrix.transvection, Matrix.single, KubotaRankTwo.n]
    apply Units.ext
    ext i j
    apply Prod.ext
    · funext w
      exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inl w) => M i j)
        ((KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inl w)).trans (ht (Sum.inl w)).symm)
    · apply Subtype.ext
      funext q
      exact congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M i j)
        ((KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inr q)).trans (ht (Sum.inr q)).symm)
  obtain ⟨A, hA, h10, h01⟩ := t.property
  let B := A * Matrix.GeneralLinearGroup.transvection 0 1 (by decide) x
  have hB : B 1 0 = 0 := by
    simp [B, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection, h10]
  refine ⟨B, hB, ?_⟩
  have he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B =
      KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) := by
    simp only [B, map_mul, hroot, hA]
  change _ = KPLiteralExceptionalResidue.adelicHeightProjection F
    (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ _)
  rw [← he]
  rfl

theorem chamber_jet_majorants
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K)
    (P : Set ℂ) (hP : IsCompact P)
    (hPc : P ⊆ {s : ℂ | (1 : ℝ) / 3 < s.re})
    (C : Set (G F ζ hζ)) (hC : IsCompact C)
    (j : KPGlobalResidualConstruction.Jet F) :
    ∃ b : KPChamberBruhatTwoCells.RationalQuotient F → ℝ,
      Summable b ∧ ∀ c s, s ∈ P → ∀ g, g ∈ C →
        ‖rightJet F ζ hζ j
          (fun a => compactExtension F ζ hζ K hK (f.val 0) s
            (rationalLift F ζ hζ (Quotient.out c) * a)) g‖ ≤ b c := by
  rcases j with ⟨n, v⟩
  by_cases hn : n = 0
  · subst n
    obtain ⟨b, hb, hbound⟩ := chamber_scalar_compact_majorants F ζ hζ K hK f P hP hPc C hC
    refine ⟨b, hb, ?_⟩
    intro c s hs g hg
    rw [rightJet_compactExtension_rational_eq, rightJet_zero]
    exact hbound c s hs g hg
  · by_cases hne : P.Nonempty
    · obtain ⟨s₀, hs₀, hmin⟩ := hP.exists_isMinOn hne Complex.continuous_re.continuousOn
      obtain ⟨s₁, hs₁, hmax⟩ := hP.exists_isMaxOn hne Complex.continuous_re.continuousOn
      have hprofile : ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ P,
          ∀ (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K),
          ‖rightJet F ζ hζ ⟨n, v⟩ (f.val s) (t.val * k.val)‖ ≤
            B * (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^
              ((2 : ℝ) / 3 + s.re) := by
        letI := KPLiteralExceptionalResidue.actualR_normal F ζ hζ
        letI := KPLiteralExceptionalResidue.actualR_cocompact F ζ hζ
        letI : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
        letI : CompactSpace P := isCompact_iff_compactSpace.mp hP
        let Q := KPGlobalTorusFunctionData.E F ζ hζ ⧸ KPGlobalCenterRationalCharacter.R F ζ hζ
        let profile : KPGlobalTorusFunctionData.E F ζ hζ → K × P → ℝ := fun t p =>
          ‖rightJet F ζ hζ ⟨n, v⟩ (f.val p.2.val) (t.val * p.1.val)‖ /
            (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^
              ((2 : ℝ) / 3 + p.2.val.re)
        have hcontinuous : Continuous (fun p : KPGlobalTorusFunctionData.E F ζ hζ × (K × P) =>
            profile p.1 p.2) := by
          simpa only [profile, rightJet] using
            JointProfile.literal_normalized_jet_profile_continuous F ζ hζ K hK f P hP ⟨n, v⟩
        let u : Q → K × P → ℝ := Quotient.lift profile (by
          intro a b hab
          funext p
          have hr : a⁻¹ * b ∈ KPGlobalCenterRationalCharacter.R F ζ hζ :=
            QuotientGroup.leftRel_apply.mp hab
          have hr' : b * a⁻¹ ∈ KPGlobalCenterRationalCharacter.R F ζ hζ := by
            simpa only [← mul_assoc, mul_inv_cancel, one_mul] using
              (KPLiteralExceptionalResidue.actualR_normal F ζ hζ).conj_mem (a⁻¹ * b) hr a
          have h := normalized_rightJet_R_invariant F ζ hζ K f p.2.val ⟨n, v⟩
            ⟨b * a⁻¹, hr'⟩ a p.1.val
          simpa only [profile, mul_assoc, inv_mul_cancel, mul_one] using h.symm)
        have hu : Continuous (fun p : Q × (K × P) => u p.1 p.2) := by
          have hid : IsOpenQuotientMap (id : K × P → K × P) :=
            ⟨Function.surjective_id, continuous_id, IsOpenMap.id⟩
          exact (QuotientGroup.isOpenQuotientMap_mk.prodMap hid).isQuotientMap.continuous_iff.mpr
            hcontinuous
        obtain ⟨B, hbound⟩ := (isCompact_univ.image hu).bddAbove
        refine ⟨max 0 B, le_max_left _ _, fun s hs t k => ?_⟩
        have h := (hbound ⟨(QuotientGroup.mk t, (k, ⟨s, hs⟩)), Set.mem_univ _, rfl⟩).trans
          (le_max_right 0 B)
        have hdpos : 0 < (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) :=
          NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
        exact (div_le_iff₀ (Real.rpow_pos_of_pos hdpos _)).mp h
      obtain ⟨B, hB, hb⟩ := hprofile
      obtain ⟨m, hm, hlow⟩ := chamberCoset_compact_covered_height_lower_bound F ζ hζ C hC
      obtain ⟨mK, M, hmK, hmKM, hdist⟩ :=
        KPLiteralExceptionalResidue.actualBaseRowHeight_compact_upper_bounds F ζ hζ K hK.1
      have hM : 0 < M := hmK.trans_le hmKM
      let d : ℝ := M⁻¹ * m
      have hd : 0 < d := mul_pos (inv_pos.mpr hM) hm
      let a₀ : ℝ := 2 / 3 + s₀.re
      let a₁ : ℝ := 2 / 3 + s₁.re
      have ha₀ : 1 < a₀ := by
        dsimp [a₀]
        have := hPc hs₀
        simp only [Set.mem_setOf_eq] at this
        linarith
      let D : ℝ := B * (d ^ (-2 * a₀) + d ^ (-2 * a₁))
      refine ⟨fun c => D * KPHeightSeries.term Projectivization.mulHeight a₀
        (KPLiteralExceptionalResidue.chamberCosetIndex F c),
        ((KPHeightSeries.relativeHeight_summable_tail F a₀ ha₀).1.comp_injective
          (KPLiteralExceptionalResidue.chamberCosetIndex_injective F)).mul_left D, ?_⟩
      intro c s hs g hg
      rw [rightJet_compactExtension_rational_eq]
      let a : ℝ := 2 / 3 + s.re
      have ha : 1 < a := by
        dsimp [a]
        have := hPc hs
        simp only [Set.mem_setOf_eq] at this
        linarith
      have hslo : s₀.re ≤ s.re := hmin hs
      have hshi : s.re ≤ s₁.re := hmax hs
      have ha0 : a₀ ≤ a := by dsimp [a₀, a]; linarith
      have ha1 : a ≤ a₁ := by dsimp [a₁, a]; linarith
      obtain ⟨t, x, k, he⟩ := hK.2.1 (rationalLift F ζ hζ (Quotient.out c) * g)
      obtain ⟨A, hA, hproj⟩ := jet_upper_projection F ζ hζ t x
      have hdist' := (hdist A k hA).2
      rw [hproj, ← map_mul, ← he, KPLiteralExceptionalResidue.actualBaseRowHeight_rational_mul] at hdist'
      let H := KPChamberHeight.height F (KPLiteralExceptionalResidue.actualBaseRowLine F)
        (KPLiteralExceptionalResidue.coveredHeightProjection F ζ hζ
          (t.val * KPGlobalTorusFunctionData.N F ζ hζ x))
      let Hc := Projectivization.mulHeight (KPLiteralExceptionalResidue.chamberCosetIndex F c)
      have hH : 0 < H := KPChamberHeight.height_pos F _ _
      have hHc : 0 < Hc := Projectivization.mulHeight_pos _
      have hHc1 : 1 ≤ Hc := Projectivization.one_le_mulHeight _
      have hgeom : d * Hc ≤ H := by
        change (M⁻¹ * m) * Hc ≤ H
        rw [mul_assoc]
        apply (inv_mul_le_iff₀ hM).mpr
        exact (hlow c g hg).trans hdist'
      have hp : H ^ (-2 * a) ≤ (d * Hc) ^ (-2 * a) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hd hHc) hgeom (by linarith)
      have hpindex : Hc ^ (-2 * a) ≤ Hc ^ (-2 * a₀) :=
        Real.rpow_le_rpow_of_exponent_le hHc1 (by linarith)
      have hpconst : d ^ (-2 * a) ≤ d ^ (-2 * a₀) + d ^ (-2 * a₁) := by
        by_cases hd1 : 1 ≤ d
        · exact (Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)).trans
            (le_add_of_nonneg_right (Real.rpow_nonneg hd.le _))
        · exact (Real.rpow_le_rpow_of_exponent_ge hd (le_of_not_ge hd1) (by linarith)).trans
            (le_add_of_nonneg_left (Real.rpow_nonneg hd.le _))
      have hdelta : (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a =
          H ^ (-2 * a) := by
        rw [← KPLiteralExceptionalResidue.actualBaseRowHeight_torus_root_modulus F ζ hζ t x]
        simpa only [Int.cast_neg, Int.cast_ofNat] using
          (Real.rpow_intCast_mul hH.le (-2) a).symm
      calc
        ‖rightJet F ζ hζ ⟨n, v⟩ (f.val s) (rationalLift F ζ hζ (Quotient.out c) * g)‖
            = ‖rightJet F ζ hζ ⟨n, v⟩ (f.val s) (t.val * k.val)‖ := by
              rw [he, rightJet_torus_root]
        _ ≤ B * (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ a := hb s hs t k
        _ = B * H ^ (-2 * a) := by rw [hdelta]
        _ ≤ B * (d * Hc) ^ (-2 * a) := mul_le_mul_of_nonneg_left hp hB
        _ = B * (d ^ (-2 * a) * Hc ^ (-2 * a)) := by
          rw [Real.mul_rpow hd.le hHc.le]
        _ ≤ B * ((d ^ (-2 * a₀) + d ^ (-2 * a₁)) * Hc ^ (-2 * a₀)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpconst hpindex (Real.rpow_nonneg hHc.le _)
              (by positivity)) hB
        _ = D * KPHeightSeries.term Projectivization.mulHeight a₀
            (KPLiteralExceptionalResidue.chamberCosetIndex F c) := by
          dsimp [D, Hc, KPHeightSeries.term]
          ring
    · refine ⟨0, summable_zero, ?_⟩
      intro c s hs g hg
      exact (hne ⟨s, hs⟩).elim

end DedekindZetaZeroFree.KPLiteralChamber

end
end
