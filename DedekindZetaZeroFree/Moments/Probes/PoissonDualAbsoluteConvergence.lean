module

public import DedekindZetaZeroFree.Moments.Probes.PoissonJointAbsoluteMass

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory

variable {F : Type} [Field F] [NumberField F]

local instance dualAbsoluteLocalMeasurable (A : SArithmeticData F) :
    MeasurableSpace (SLocalProduct F A.Sf) := borel _

local instance dualAbsoluteLocalBorel (A : SArithmeticData F) :
    BorelSpace (SLocalProduct F A.Sf) := ⟨rfl⟩

local instance dualAbsoluteG1Measurable (A : SArithmeticData F) :
    MeasurableSpace A.G1 := borel _
local instance dualAbsoluteG1Borel (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

namespace ProbePoissonDualAbsolute

abbrev Index (A : SArithmeticData F) :=
  A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior × ThetaReflectionData.Row A

def kernel (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (e : (v : ↥A.Sf) → AddChar (v.val.adicCompletion F) Circle)
    (μ : Measure (SLocalProduct F A.Sf))
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (X Y Z : ℝ) (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS)
    (n : A.Exterior) (h : A.R) (t : A.G1) : ℂ :=
  let qA := A.exteriorNorm c.val * A.exteriorNorm n ^ 3
  ((Real.sqrt X / Y : ℝ) : ℂ) * (W1 (A.exteriorNorm s / Y) : ℂ) *
    (D.gammaTwo c * D.theta (ThetaReflectionData.forwardModulus A D c n) /
      (((Real.sqrt (A.exteriorNorm c.val) : ℂ) * (A.exteriorNorm n : ℂ)) *
        (qA : ℂ))) *
    (thetaReflectionGaussian (qA / Z) : ℂ) *
    comparisonPoissonFiniteCoefficient F A D c n s h *
    ProbeWeight.fourier F A.Sf e μ W0
      ((ProbeSheet.localUnits A t.val).val *
        ProbePoissonSheet.frequency A X (D.generator s)
          (ThetaReflectionData.forwardModulus A D c n) h)

def term (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (X Y Z : ℝ) (i : Index A) (t : A.G1) : ℂ :=
  kernel A P.coefficients P.finiteTrace P.additiveMeasure P.W0 P.W1
    X Y Z i.1 i.2.1 i.2.2.1 i.2.2.2.val t

theorem principalNorm_generator (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (s : A.Exterior) :
    ProbePoissonSheet.principalNorm A (D.generator s) = A.exteriorNorm s := by
  rw [(ProbePoissonSheet.principalNorm_eq_modulus A _ (D.generates s).1).1]
  exact ProbeJointAbsoluteMass.q_generator A D s

theorem term_eq_kernel (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (X Y Z : ℝ) (i : Index A) (t : A.G1) :
    term A σ η hS P X Y Z i t =
      ProbeJointAbsoluteMass.kernel A σ η hS P X Y Z i t := by
  have hq := principalNorm_generator A P.coefficients i.1
  have hfreq : ProbePoissonSheet.frequency A X (P.coefficients.generator i.1)
        (ThetaReflectionData.forwardModulus A P.coefficients i.2.1 i.2.2.1) i.2.2.2.val =
      ProbeJointAbsoluteMass.frequency A P.coefficients X i.1 i.2.1 i.2.2.1 i.2.2.2 := by
    simp only [ProbePoissonSheet.frequency, ProbeJointAbsoluteMass.frequency, hq]
  unfold term kernel ProbeJointAbsoluteMass.kernel ProbeJointAbsoluteMass.lambda
    ProbeJointAbsoluteMass.modulusNorm ThetaReflectionData.forwardArithmeticWeight
  rw [hfreq]
  push_cast
  ring_nf

theorem summable_sumOrbit (A : SArithmeticData F) (ρ : ℝ) (hρ : 1 < ρ) :
    Summable (fun o : ProbeOrbitNormSum.Orbit A =>
      (ProbeOrbitNormSum.orbitNorm A o) ^ (-ρ)) :=
  ProbeOrbitNormSum.orbit_norm_rpow_summable A ρ hρ

theorem summable_sumS (A : SArithmeticData F) (W1 : ProbeRealAnnularWeight)
    (Y : ℝ) (hY : 0 < Y) :
    Summable (fun s : A.Exterior => |W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s) :=
  ProbeJointAbsoluteMass.summable_outerMoment A W1 Y hY

theorem summable_sumCN (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (ρ Z : ℝ) (hρ : 1 < ρ) (hZ : 0 < Z) :
    Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      ‖P.coefficients.gammaTwo i.1 *
          P.coefficients.theta
            (ThetaReflectionData.forwardModulus A P.coefficients i.1 i.2)‖ *
        |thetaReflectionGaussian
          (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z)| *
        (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3) ^ ρ /
        (Real.sqrt (A.exteriorNorm i.1.val) * A.exteriorNorm i.2)) := by
  obtain ⟨C, hC, hk⟩ :=
    ProbePoissonGaussianRowBound.gaussian_row_domination A ι η hS ρ Z hρ hZ
  have hrow : Summable (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
      ProbePoissonGaussianRowBound.rowMass A P.coefficients ρ Z i.1 i.2) :=
    (hk P).2.2.2.1
  have heq : (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
        ProbePoissonGaussianRowBound.rowMass A P.coefficients ρ Z i.1 i.2) =
      (fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
        ‖P.coefficients.gammaTwo i.1 *
            P.coefficients.theta
              (ThetaReflectionData.forwardModulus A P.coefficients i.1 i.2)‖ *
          |thetaReflectionGaussian
            (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3 / Z)| *
          (A.exteriorNorm i.1.val * A.exteriorNorm i.2 ^ 3) ^ ρ /
          (Real.sqrt (A.exteriorNorm i.1.val) * A.exteriorNorm i.2)) := by
    funext i
    simp only [ProbePoissonGaussianRowBound.rowMass,
      ThetaReflectionData.forwardArithmeticWeight, norm_mul]
    ring
  rwa [heq] at hrow

theorem term_continuous (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (X Y Z : ℝ) (i : Index A) : Continuous (term A ι η hS P X Y Z i) := by
  have hf := ProbeSheetFourierMellinBounds.raw_fourier_continuous A P.finiteTrace P.continuousTrace
    P.additiveMeasure P.additiveHaar P.W0 P.annular P.compactSupport
  have hl : Continuous (fun t : A.G1 => (ProbeSheet.localUnits A t.val).val) :=
    Units.continuous_val.comp ((ProbeSheet.continuous_localUnits A).comp continuous_subtype_val)
  have he : term A ι η hS P X Y Z i = ProbeJointAbsoluteMass.kernel A ι η hS P X Y Z i :=
    funext (term_eq_kernel A ι η hS P X Y Z i)
  rw [he]
  unfold ProbeJointAbsoluteMass.kernel
  exact continuous_const.mul (hf.comp (hl.mul continuous_const))

theorem rowMass_eq (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (ρ Z : ℝ) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) :
    ProbePoissonGaussianRowBound.rowMass A D ρ Z c n =
      ‖D.gammaTwo c * D.theta (ThetaReflectionData.forwardModulus A D c n)‖ *
        |thetaReflectionGaussian (A.exteriorNorm c.val * A.exteriorNorm n ^ 3 / Z)| *
        (A.exteriorNorm c.val * A.exteriorNorm n ^ 3) ^ ρ /
        (Real.sqrt (A.exteriorNorm c.val) * A.exteriorNorm n) := by
  simp only [ProbePoissonGaussianRowBound.rowMass,
    ThetaReflectionData.forwardArithmeticWeight, norm_mul]
  ring

set_option maxHeartbeats 1000000 in

theorem orbit_mass_row_majorant (A : SArithmeticData F) (ι : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A ι η hS)
    (hne : ∀ v, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A P.multiplicativeMeasure P.domain.measure)
    (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
      ∀ (r : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A),
      ProbeOrbitNormSum.IsRepresentativeSection A r →
      (∑' i : ProbeJointAbsoluteMass.OrbitIndex A, ∫ t : A.G1,
        ‖ProbeJointAbsoluteMass.kernel A ι η hS P X Y Z
          (i.1, i.2.1, i.2.2.1, r i.2.2.2) t‖ ∂P.domain.measure) ≤
      C * Real.sqrt X * X ^ (-ρ) / Y *
        (∑' s : A.Exterior, |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s) *
        (∑' p : ExteriorSquarefreeIdeal A.cS × A.Exterior,
          ProbePoissonGaussianRowBound.rowMass A P.coefficients ρ Z p.1 p.2) *
        (∑' o : ProbeOrbitNormSum.Orbit A, ProbeOrbitNormSum.orbitNorm A o ^ (-ρ)) := by
  obtain ⟨C, hC, hb⟩ := ProbeJointAbsoluteMass.integrated_orbit_mass_bound A ι η hS P
    hne hnormalized ρ (lt_trans zero_lt_one hρ)
  refine ⟨C, hC, ?_⟩
  intro X Y Z hX hY hZ r hr
  let f := fun s : A.Exterior => |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s
  let g := fun p : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
    ProbePoissonGaussianRowBound.rowMass A P.coefficients ρ Z p.1 p.2
  let o := fun o : ProbeOrbitNormSum.Orbit A => ProbeOrbitNormSum.orbitNorm A o ^ (-ρ)
  have hf : Summable f := summable_sumS A P.W1 Y hY
  have hg : Summable g := by
    simpa only [g, rowMass_eq] using summable_sumCN A ι η hS P ρ Z hρ hZ
  have ho : Summable o := summable_sumOrbit A ρ hρ
  have hf0 (s) : 0 ≤ f s := mul_nonneg (abs_nonneg _) (A.exteriorNorm_pos s).le
  have hg0 (p) : 0 ≤ g p := by
    dsimp [g]
    rw [rowMass_eq]
    exact div_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg (mul_pos (A.exteriorNorm_pos p.1.val)
        (pow_pos (A.exteriorNorm_pos p.2) 3)).le _))
      (mul_pos (Real.sqrt_pos.mpr (A.exteriorNorm_pos p.1.val))
        (A.exteriorNorm_pos p.2)).le
  have ho0 (a) : 0 ≤ o a := Real.rpow_nonneg (ProbeOrbitNormSum.orbitNorm_pos A a).le _
  have hfg : Summable (fun i : A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior) =>
      f i.1 * g i.2) := summable_mul_of_summable_norm (f := f) (g := g)
    (by simpa only [Real.norm_of_nonneg (hf0 _)] using hf)
    (by simpa only [Real.norm_of_nonneg (hg0 _)] using hg)
  have hall : Summable (fun i :
      (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) × ProbeOrbitNormSum.Orbit A =>
      (f i.1.1 * g i.1.2) * o i.2) := summable_mul_of_summable_norm
    (f := fun i : A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior) => f i.1 * g i.2)
    (g := o)
    (by simpa only [Real.norm_of_nonneg (mul_nonneg (hf0 _) (hg0 _))] using hfg)
    (by simpa only [Real.norm_of_nonneg (ho0 _)] using ho)
  let e : ProbeJointAbsoluteMass.OrbitIndex A ≃
      (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) × ProbeOrbitNormSum.Orbit A :=
    { toFun := fun i => ((i.1, (i.2.1, i.2.2.1)), i.2.2.2)
      invFun := fun i => (i.1.1, i.1.2.1, i.1.2.2, i.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmajor : Summable (fun i : ProbeJointAbsoluteMass.OrbitIndex A =>
      C * Real.sqrt X * X ^ (-ρ) / Y * f i.1 * g (i.2.1, i.2.2.1) * o i.2.2.2) := by
    have he := e.summable_iff.mpr hall
    simpa only [e, Function.comp_apply, Equiv.coe_fn_mk, mul_assoc] using
      he.mul_left (C * Real.sqrt X * X ^ (-ρ) / Y)
  have hm := ProbeJointAbsoluteMass.whole_group_orbit_mass_summable A ι η hS P hne
    hnormalized X Y Z hX hY hZ r hr
  calc
    _ ≤ ∑' i : ProbeJointAbsoluteMass.OrbitIndex A,
        C * Real.sqrt X * X ^ (-ρ) / Y * f i.1 * g (i.2.1, i.2.2.1) * o i.2.2.2 := by
      apply hm.tsum_le_tsum _ hmajor
      intro i
      have hq : ProbeSheetTranslation.q A (r i.2.2.2).val (r i.2.2.2).property =
          ProbeOrbitNormSum.orbitNorm A i.2.2.2 := by
        unfold ProbeSheetTranslation.q
        rw [← ProbeOrbitNormSum.orbitNorm_eq_snorm A (r i.2.2.2)
          (ProbeSheetTranslation.fieldUnit A _ _) rfl, hr i.2.2.2]
      simpa only [hq] using hb X Y Z hX hY i.1 i.2.1 i.2.2.1 (r i.2.2.2)
    _ = _ := by
      have heq : (∑' i : ProbeJointAbsoluteMass.OrbitIndex A,
          f i.1 * g (i.2.1, i.2.2.1) * o i.2.2.2) =
          (∑' s, f s) * (∑' p, g p) * (∑' a, o a) := by
        rw [← e.symm.tsum_eq]
        change (∑' i : (A.Exterior × (ExteriorSquarefreeIdeal A.cS × A.Exterior)) ×
          ProbeOrbitNormSum.Orbit A, (f i.1.1 * g i.1.2) * o i.2) = _
        rw [← hfg.tsum_mul_tsum ho hall, ← hf.tsum_mul_tsum hg hfg]
      simp_rw [mul_assoc, tsum_mul_left]
      simp_rw [mul_assoc] at heq
      rw [heq]

end ProbePoissonDualAbsolute

set_option maxHeartbeats 1000000 in

theorem probe_poisson_dual_absolute (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (σ₀ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ₀ η hS)
    (hnontrivial : ∀ v : ↥A.Sf, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A
      P.multiplicativeMeasure P.domain.measure) :
    ∀ ρ : ℝ, 1 < ρ → ∃ Cρ : ℝ, 0 ≤ Cρ ∧
      ∀ (X Y Z : ℝ), 0 < X → 0 < Y → 0 < Z →
      let k := ProbePoissonDualAbsolute.term A σ₀ η hS P X Y Z
      let qA := fun (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) =>
        A.exteriorNorm c.val * A.exteriorNorm n ^ 3
      let sumS := fun s : A.Exterior =>
        |P.W1 (A.exteriorNorm s / Y)| * A.exteriorNorm s
      let sumCN := fun i : ExteriorSquarefreeIdeal A.cS × A.Exterior =>
        ‖P.coefficients.gammaTwo i.1 *
            P.coefficients.theta
              (ThetaReflectionData.forwardModulus A P.coefficients i.1 i.2)‖ *
          |thetaReflectionGaussian (qA i.1 i.2 / Z)| *
          (qA i.1 i.2 : ℝ) ^ ρ /
          (Real.sqrt (A.exteriorNorm i.1.val) * A.exteriorNorm i.2)
      let sumOrbit := fun o : ProbeOrbitNormSum.Orbit A =>
        (ProbeOrbitNormSum.orbitNorm A o) ^ (-ρ)
      Summable sumS ∧ Summable sumCN ∧ Summable sumOrbit ∧
      (∀ i : ProbePoissonDualAbsolute.Index A,
        Measurable (k i) ∧ IntegrableOn (k i) P.domain.domain P.domain.measure) ∧
      Summable (fun i : ProbePoissonDualAbsolute.Index A =>
        ∫ t in P.domain.domain, ‖k i t‖ ∂P.domain.measure) ∧
      (∫⁻ t in P.domain.domain,
        ∑' i : ProbePoissonDualAbsolute.Index A,
          ENNReal.ofReal ‖k i t‖ ∂P.domain.measure) < ⊤ ∧
      (∑' i : ProbePoissonDualAbsolute.Index A,
        ∫ t in P.domain.domain, ‖k i t‖ ∂P.domain.measure) ≤
        Cρ * Real.sqrt X * X ^ (-ρ) / Y *
          (∑' s : A.Exterior, sumS s) *
          (∑' i : ExteriorSquarefreeIdeal A.cS × A.Exterior, sumCN i) *
          (∑' o : ProbeOrbitNormSum.Orbit A, sumOrbit o) ∧
      (∀ᵐ t ∂P.domain.measure.restrict P.domain.domain,
        Summable (fun i : ProbePoissonDualAbsolute.Index A => ‖k i t‖) ∧
        Summable (fun i : ProbePoissonDualAbsolute.Index A => k i t)) ∧
      IntegrableOn (fun t => ∑' i : ProbePoissonDualAbsolute.Index A, k i t)
        P.domain.domain P.domain.measure ∧
      Summable (fun i : ProbePoissonDualAbsolute.Index A =>
        ∫ t in P.domain.domain, k i t ∂P.domain.measure) ∧
      (∫ t in P.domain.domain,
        ∑' i : ProbePoissonDualAbsolute.Index A, k i t ∂P.domain.measure) =
        (∑' i : ProbePoissonDualAbsolute.Index A,
          ∫ t in P.domain.domain, k i t ∂P.domain.measure) ∧
      (∀ (ι : Type) (e : ι ≃ ProbePoissonDualAbsolute.Index A),
        Summable (fun j : ι => ∫ t in P.domain.domain, ‖k (e j) t‖ ∂P.domain.measure) ∧
        (∫ t in P.domain.domain, ∑' j : ι, k (e j) t ∂P.domain.measure) =
          (∑' j : ι, ∫ t in P.domain.domain, k (e j) t ∂P.domain.measure) ∧
        (∑' j : ι, ∫ t in P.domain.domain, k (e j) t ∂P.domain.measure) =
          (∑' i : ProbePoissonDualAbsolute.Index A,
            ∫ t in P.domain.domain, k i t ∂P.domain.measure)) := by
  intro ρ hρ
  obtain ⟨C, hC, hb⟩ := ProbePoissonDualAbsolute.orbit_mass_row_majorant A σ₀ η hS P
    hnontrivial hnormalized ρ hρ
  refine ⟨C, hC, ?_⟩
  intro X Y Z hX hY hZ
  dsimp only
  let k := ProbePoissonDualAbsolute.term A σ₀ η hS P X Y Z
  have heq : k = ProbeJointAbsoluteMass.kernel A σ₀ η hS P X Y Z :=
    funext (fun i => funext (ProbePoissonDualAbsolute.term_eq_kernel A σ₀ η hS P X Y Z i))
  have hcount := ProbeOrbitNormSum.indices_countable A
  letI : Countable (ProbeOrbitNormSum.Nonzero A) := hcount.1
  letI : Countable A.Exterior := hcount.2.2.2.2.2.1
  letI : Countable (ExteriorSquarefreeIdeal A.cS) :=
    inferInstanceAs (Countable {I : A.Exterior // Squarefree I.val})
  have hiG := ProbeJointAbsoluteMass.kernel_integrable A σ₀ η hS P hnontrivial
    hnormalized X Y Z hX
  have hi : ∀ i : ProbePoissonDualAbsolute.Index A,
      IntegrableOn (k i) P.domain.domain P.domain.measure := by
    intro i
    rw [heq]
    exact (hiG i).integrableOn
  let r : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A := Quotient.out
  have hr : ProbeOrbitNormSum.IsRepresentativeSection A r := fun o => Quotient.out_eq o
  have ho := ProbeJointAbsoluteMass.whole_group_orbit_mass_summable A σ₀ η hS P
    hnontrivial hnormalized X Y Z hX hY hZ r hr
  have hunfold := ProbeJointAbsoluteMass.norm_unfolding_raw A P.domain r hr
    (fun i t => ENNReal.ofReal ‖k i t‖)
    (fun s c n h γ t => by
      rw [heq]
      exact congrArg (fun z : ℂ => ENNReal.ofReal ‖z‖)
        (ProbeJointAbsoluteMass.kernel_gamma_translate A σ₀ η hS P X Y Z s c n h γ t))
  obtain ⟨hs, hsum⟩ := ProbeJointNormMassTransfer.norm_mass_transfer
    P.domain.measure P.domain.domain k
    (fun i : ProbeJointAbsoluteMass.OrbitIndex A => k (i.1,i.2.1,i.2.2.1,r i.2.2.2))
    hi (fun i => by rw [heq]; exact hiG _) (by simpa only [heq] using ho) hunfold
  have hex := ProbeJointAbsoluteMass.joint_series_exchanges
    (P.domain.measure.restrict P.domain.domain) k hi hs
  have hfinite : (∫⁻ t in P.domain.domain,
      ∑' i : ProbePoissonDualAbsolute.Index A, ENNReal.ofReal ‖k i t‖
        ∂P.domain.measure) < ⊤ := by
    simp_rw [ofReal_norm]
    rw [lintegral_tsum (fun i => (hi i).aestronglyMeasurable.enorm)]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    exact hs.tsum_ofReal_ne_top.lt_top
  have hbound := hb X Y Z hX hY hZ r hr
  rw [← heq, ← hsum] at hbound
  simp_rw [ProbePoissonDualAbsolute.rowMass_eq] at hbound
  refine ⟨ProbePoissonDualAbsolute.summable_sumS A P.W1 Y hY,
    ProbePoissonDualAbsolute.summable_sumCN A σ₀ η hS P ρ Z hρ hZ,
    ProbePoissonDualAbsolute.summable_sumOrbit A ρ hρ,
    (fun i => ⟨(ProbePoissonDualAbsolute.term_continuous A σ₀ η hS P X Y Z i).measurable,
      hi i⟩), hs, hfinite, hbound, hex.1, hex.2.1, hex.2.2.1.of_norm,
    hex.2.2.2.1, ?_⟩
  intro J e
  have hs' : Summable (fun j : J => ∫ t in P.domain.domain, ‖k (e j) t‖ ∂P.domain.measure) :=
    e.summable_iff.mpr hs
  have heint : (∑' j : J, ∫ t in P.domain.domain, k (e j) t ∂P.domain.measure) =
      ∑' i : ProbePoissonDualAbsolute.Index A, ∫ t in P.domain.domain, k i t ∂P.domain.measure :=
    e.tsum_eq (fun i => ∫ t in P.domain.domain, k i t ∂P.domain.measure)
  exact ⟨hs', (hex.2.2.2.2.1 J e).trans heint.symm, heint⟩

end
end DedekindZetaZeroFree
