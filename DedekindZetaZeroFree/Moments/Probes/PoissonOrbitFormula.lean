module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerTraceSummation
public import DedekindZetaZeroFree.Moments.Probes.NormalizedPoissonRow
public import DedekindZetaZeroFree.Moments.Probes.PoissonDualAbsoluteConvergence
public import DedekindZetaZeroFree.Moments.Probes.IntegratedSquarefreeCubeRowExpansion

@[expose] public section

namespace DedekindZetaZeroFree.ProbePoissonOrbitFormula
noncomputable section
open scoped Classical NumberField
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

local instance (A : SArithmeticData F) : MeasurableSpace A.G1 := borel _

local instance (A : SArithmeticData F) : BorelSpace A.G1 := ⟨rfl⟩

local instance (A : SArithmeticData F) : MeasurableSpace (SLocalProduct F A.Sf) := borel _

def qA (A : SArithmeticData F) (c : ExteriorSquarefreeIdeal A.cS)
    (n : A.Exterior) : ℝ :=
  A.exteriorNorm c.val * A.exteriorNorm n ^ 3

def arithmeticFactor (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A)
    (Z : ℝ) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) : ℂ :=
  (D.gammaTwo c * D.theta (ThetaReflectionData.forwardModulus A D c n) /
    (((Real.sqrt (A.exteriorNorm c.val) : ℂ) * (A.exteriorNorm n : ℂ)) *
      (qA A c n : ℂ))) * (thetaReflectionGaussian (qA A c n / Z) : ℂ)

def orbitRow (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (X : ℝ) (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS)
    (n : A.Exterior) (h : ProbeOrbitNormSum.Nonzero A) : ℂ :=
  comparisonPoissonFiniteCoefficient F A P.coefficients c n s h.val *
    ProbeSheet.envelope A P.finiteTrace P.additiveMeasure P.domain.measure P.W0
      (X * ProbeOrbitNormSum.orbitNorm A (ProbeOrbitNormSum.orbitMk A h) / qA A c n)

abbrev Index (A : SArithmeticData F) :=
  A.Exterior × ExteriorSquarefreeIdeal A.cS × A.Exterior × ProbeOrbitNormSum.Orbit A

def term (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (X Y Z : ℝ) (i : Index A) : ℂ :=
  ((Real.sqrt X / Y : ℝ) : ℂ) * (P.W1 (A.exteriorNorm i.1 / Y) : ℂ) *
    arithmeticFactor A P.coefficients Z i.2.1 i.2.2.1 *
    orbitRow A σ η hS P X i.1 i.2.1 i.2.2.1 (ρ i.2.2.2)

private theorem q_nonzero (A : SArithmeticData F)
    (h : ProbeOrbitNormSum.Nonzero A) :
    ProbeSheetTranslation.q A h.val h.property =
      ProbeOrbitNormSum.orbitNorm A (ProbeOrbitNormSum.orbitMk A h) :=
  (ProbeOrbitNormSum.orbitNorm_eq_snorm A h
    (ProbeSheetTranslation.fieldUnit A h.val h.property) rfl).symm

section Assembly
variable (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (hne : ∀ v : ↥A.Sf, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A
      P.multiplicativeMeasure P.domain.measure)

include hne hnormalized in
private theorem fourier_integral (X : ℝ) (hX : 0 < X)
    (s : A.Exterior) (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior)
    (h : ProbeOrbitNormSum.Nonzero A) :
    (∫ t : A.G1, ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
      ((ProbeSheet.localUnits A t.val).val *
        ProbeJointAbsoluteMass.frequency A P.coefficients X s c n h) ∂P.domain.measure) =
      ProbeSheet.envelope A P.finiteTrace P.additiveMeasure P.domain.measure P.W0
        (X * ProbeOrbitNormSum.orbitNorm A (ProbeOrbitNormSum.orbitMk A h) / qA A c n) := by
  obtain ⟨C, hC, hb⟩ := probe_sheet_shape_translation_fraction F A
    P.finiteTrace P.continuousTrace P.traceCompatible hne
    P.additiveMeasure P.multiplicativeMeasure P.domain.measure
    P.additiveHaar P.multiplicativeHaar P.domain.haar hnormalized
    (Classical.arbitrary _) P.W0 P.W1 P.annular P.compactSupport P.supportUnits
    2 (by norm_num)
  have ha := mul_ne_zero (P.coefficients.generates c.val).1
    (pow_ne_zero 3 (P.coefficients.generates n).1)
  have hb' := (hb X hX (P.coefficients.generator s)
    (ThetaReflectionData.forwardModulus A P.coefficients c n) h.val
    (P.coefficients.generates s).1 ha h.property).2.2.2.1
  simp_rw [ProbeJointAbsoluteMass.frequency_eq_fractionPoint A P.coefficients X hX]
  simpa only [ProbeSheetTranslation.translatedFourier, Units.val_mul, q_nonzero,
    ProbeJointAbsoluteMass.q_forwardModulus, ProbeJointAbsoluteMass.modulusNorm, qA] using hb'

include hne hnormalized in

theorem orbitIntegral_eq_term
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (X Y Z : ℝ) (hX : 0 < X) (i : Index A) :
    ProbeJointAbsoluteMass.orbitIntegral A σ η hS P X Y Z ρ i =
      term A σ η hS P ρ X Y Z i := by
  unfold ProbeJointAbsoluteMass.orbitIntegral ProbeJointAbsoluteMass.kernel
  rw [integral_const_mul, fourier_integral A σ η hS P hne hnormalized X hX]
  unfold term arithmeticFactor orbitRow ProbeJointAbsoluteMass.lambda
    ProbeJointAbsoluteMass.modulusNorm qA ThetaReflectionData.forwardArithmeticWeight
  push_cast
  ring
include hne hnormalized in

theorem summable_norm_term
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : Function.LeftInverse (ProbeOrbitNormSum.orbitMk A) ρ)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Summable (fun i : Index A => ‖term A σ η hS P ρ X Y Z i‖) := by
  have ht := (ProbeJointAbsoluteMass.orbit_integrals_absolutely_summable
    A σ η hS P hne hnormalized X Y Z hX hY hZ ρ hρ).1
  simpa only [orbitIntegral_eq_term A σ η hS P hne hnormalized ρ X Y Z hX] using ht
end Assembly

private theorem modulus_generator (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (s : A.Exterior) :
    PoissonNormalizedRow.modulus A (D.generator s) = A.exteriorNorm s :=
  ProbePoissonDualAbsolute.principalNorm_generator A D s

theorem originalRow_eq_dual (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : PoissonNormalizedRow.Normalization A σ η hS P)
    (X : ℝ) (hX : 0 < X) (s : A.Exterior)
    (c : ExteriorSquarefreeIdeal A.cS) (n : A.Exterior) (t : A.G1) :
    NormalizedProbe.originalRow A P.coefficients P.W0 X s
      (ThetaReflectionData.forwardModulus A P.coefficients c n) t =
    ((Real.sqrt X / qA A c n : ℝ) : ℂ) *
      ∑' h : ProbeOrbitNormSum.Nonzero A,
        comparisonPoissonFiniteCoefficient F A P.coefficients c n s h.val *
          ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
            ((ProbeSheet.localUnits A t.val).val *
              ProbeJointAbsoluteMass.frequency A P.coefficients X s c n h) := by
  let D := P.coefficients
  have ha := mul_ne_zero (D.generates c.val).1 (pow_ne_zero 3 (D.generates n).1)
  have hqa : PoissonNormalizedRow.modulus A (ThetaReflectionData.forwardModulus A D c n) =
      qA A c n := by
    have ha' : ThetaReflectionData.forwardModulus A D c n ≠ 0 := ha
    rw [show PoissonNormalizedRow.modulus A _ = ProbePoissonSheet.principalNorm A _ from rfl,
      (ProbePoissonSheet.principalNorm_eq_modulus A _ ha').1]
    exact ProbeJointAbsoluteMass.q_forwardModulus A D c n
  have ht := (PoissonNormalizedRow.exact_normalized_poisson_row
    A σ η hS P N (D.generator s) (ThetaReflectionData.forwardModulus A D c n)
    (D.generates s).1 ha X hX t).2.2.2
  rw [modulus_generator, hqa] at ht
  have horig (m : A.R) : PoissonNormalizedRow.originalTerm A D P.W0 (D.generator s)
      (ThetaReflectionData.forwardModulus A D c n) (D.generates s).1 X t m =
      NormalizedProbe.gaussRow A D s m *
        D.character (ThetaReflectionData.forwardModulus A D c n)
          (FiniteTransform.residueMap A.R.toSubring (ThetaReflectionData.forwardModulus A D c n) m) *
        P.W0 (sLocalDiagonal F A.Sf (m : F) * NormalizedProbe.asLocalPoint A
          (((t : A.G) * NormalizedProbe.radialSection A (A.exteriorNorm s * X))⁻¹)) := by
    simp only [PoissonNormalizedRow.originalTerm, NormalizedProbe.gaussRow, modulus_generator]
  have hfreq (h : ProbeOrbitNormSum.Nonzero A) :
      PoissonNormalizedRow.frequencyTerm A D P.finiteTrace P.additiveMeasure P.W0
        (D.generator s) (ThetaReflectionData.forwardModulus A D c n)
        (D.generates s).1 ha X t h.val =
      comparisonPoissonFiniteCoefficient F A D c n s h.val *
        ProbeWeight.fourier F A.Sf P.finiteTrace P.additiveMeasure P.W0
          ((ProbeSheet.localUnits A t.val).val *
            ProbeJointAbsoluteMass.frequency A D X s c n h) := by
    unfold PoissonNormalizedRow.frequencyTerm comparisonPoissonFiniteCoefficient
    congr 2
    simp only [PoissonNormalizedRow.frequencyPoint, ProbeJointAbsoluteMass.frequency,
      modulus_generator]
    change NormalizedProbe.asLocalPoint A ((t : A.G) *
        NormalizedProbe.radialSection A (A.exteriorNorm s * X)) * _ = _
    have hlocal (g : A.G) : NormalizedProbe.asLocalPoint A g =
        (ProbeSheet.localUnits A g).val := rfl
    simp only [hlocal, map_mul, Units.val_mul]
    simp only [NormalizedProbe.radialSection, ProbeSheet.ell,
      dif_pos (mul_pos (A.exteriorNorm_pos s) hX), mul_assoc]
  change (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ *
    (∑' m, PoissonNormalizedRow.originalTerm A D P.W0 (D.generator s)
      (ThetaReflectionData.forwardModulus A D c n) (D.generates s).1 X t m) =
    ((Real.sqrt X / qA A c n : ℝ) : ℂ) *
    (∑' h : ProbeOrbitNormSum.Nonzero A,
      PoissonNormalizedRow.frequencyTerm A D P.finiteTrace P.additiveMeasure P.W0
        (D.generator s) (ThetaReflectionData.forwardModulus A D c n)
        (D.generates s).1 ha X t h.val) at ht
  simp_rw [horig, hfreq] at ht
  exact ht

theorem exact_poisson_transformation (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : PoissonNormalizedRow.Normalization A σ η hS P)
    (hnontrivial : ∀ v : ↥A.Sf, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A
      P.multiplicativeMeasure P.domain.measure)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    NormalizedProbe.principalProbe A σ η hS P ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ =
      (∫ t in P.domain.domain, ∑' i : ProbePoissonDualAbsolute.Index A,
        ProbePoissonDualAbsolute.term A σ η hS P X Y Z i t ∂P.domain.measure) ∧
    (∫ t in P.domain.domain, ∑' i : ProbePoissonDualAbsolute.Index A,
      ProbePoissonDualAbsolute.term A σ η hS P X Y Z i t ∂P.domain.measure) =
      ∑' i : ProbePoissonDualAbsolute.Index A,
        ∫ t in P.domain.domain,
          ProbePoissonDualAbsolute.term A σ η hS P X Y Z i t ∂P.domain.measure := by
  obtain ⟨C, hC, hb⟩ := probe_poisson_dual_absolute F A σ η hS P
    hnontrivial hnormalized 2 (by norm_num)
  have hd := hb X Y Z hX hY hZ
  refine ⟨?_, hd.2.2.2.2.2.2.2.2.2.2.1⟩
  have hj := ProbeJointAbsoluteMass.exchanges_and_orbit_convergence A σ η hS P
    hnontrivial hnormalized X Y Z hX hY hZ
  simp_rw [ProbePoissonDualAbsolute.term_eq_kernel]
  rw [hj.2.2.2.1]
  have hs := hj.2.2.1.of_norm
  rw [hs.tsum_prod]
  rw [NormalizedProbe.principalProbe,
    NormalizedProbe.principal_original_integrated_row_expansion A σ η hS P X Y Z hX hY hZ,
    ← tsum_mul_left]
  apply tsum_congr
  intro s
  rw [(hs.prod_factor s).tsum_prod]
  simp only [← tsum_mul_left]
  apply tsum_congr
  intro c
  rw [((hs.prod_factor s).prod_factor c).tsum_prod]
  apply tsum_congr
  intro n
  obtain ⟨C', hC', hb'⟩ := ProbeJointAbsoluteMass.finite_absolute_mass A σ η hS P
    hnontrivial hnormalized 2 (by norm_num)
  have hi := (hb' X Y Z hX hY hZ).1
  have hn := (hb' X Y Z hX hY hZ).2.1
  have hsub : Summable (fun h : ProbeOrbitNormSum.Nonzero A =>
      ∫ t in P.domain.domain, ‖ProbeJointAbsoluteMass.kernel A σ η hS P X Y Z
        (s,c,n,h) t‖ ∂P.domain.measure) :=
    ((hn.prod_factor s).prod_factor c).prod_factor n
  rw [← integral_tsum (fun h => (hi (s,c,n,h)).aestronglyMeasurable)
    (by simpa only [ofReal_integral_norm_eq_lintegral_enorm (hi _)]
      using hsub.tsum_ofReal_ne_top)]
  simp_rw [originalRow_eq_dual A σ η hS P N X hX s c n]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [ProbeJointAbsoluteMass.kernel, mul_assoc, tsum_mul_left]
  rfl

theorem exact_orbit_formula (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (N : PoissonNormalizedRow.Normalization A σ η hS P)
    (hnontrivial : ∀ v : ↥A.Sf, P.finiteTrace v ≠ 1)
    (hnormalized : ProbeSheet.HaarDisintegration A
      P.multiplicativeMeasure P.domain.measure)
    (ρ : ProbeOrbitNormSum.Orbit A → ProbeOrbitNormSum.Nonzero A)
    (hρ : Function.LeftInverse (ProbeOrbitNormSum.orbitMk A) ρ)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Summable (fun i : Index A => ‖term A σ η hS P ρ X Y Z i‖) ∧
    NormalizedProbe.principalProbe A σ η hS P ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ =
      ((Real.sqrt X / Y : ℝ) : ℂ) *
        ∑' s : A.Exterior, (P.W1 (A.exteriorNorm s / Y) : ℂ) *
          ∑' j : ExteriorSquarefreeIdeal A.cS × A.Exterior,
            arithmeticFactor A P.coefficients Z j.1 j.2 *
              ∑' o : ProbeOrbitNormSum.Orbit A,
                orbitRow A σ η hS P X s j.1 j.2 (ρ o) ∧
    NormalizedProbe.principalProbe A σ η hS P ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ =
      ∑' i : Index A, term A σ η hS P ρ X Y Z i := by
  have hn := summable_norm_term A σ η hS P hnontrivial hnormalized
    ρ hρ X Y Z hX hY hZ
  have hp := (exact_poisson_transformation A σ η hS P N
    hnontrivial hnormalized X Y Z hX hY hZ).1
  have hu := (ProbeJointAbsoluteMass.exchanges_and_orbit_convergence A σ η hS P
    hnontrivial hnormalized X Y Z hX hY hZ).2.2.2.2.2.2 ρ hρ
  simp_rw [ProbePoissonDualAbsolute.term_eq_kernel] at hp
  have he : NormalizedProbe.principalProbe A σ η hS P ⟨X,hX⟩ ⟨Y,hY⟩ ⟨Z,hZ⟩ =
      ∑' i : Index A, term A σ η hS P ρ X Y Z i := by
    rw [hp, hu.2.2]
    apply tsum_congr
    intro i
    exact orbitIntegral_eq_term A σ η hS P hnontrivial hnormalized ρ X Y Z hX i
  refine ⟨hn, ?_, he⟩
  rw [he, hn.of_norm.tsum_prod]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro s
  let e := Equiv.prodAssoc (ExteriorSquarefreeIdeal A.cS) A.Exterior (ProbeOrbitNormSum.Orbit A)
  have hs : Summable (fun i => term A σ η hS P ρ X Y Z (s,e i)) :=
    (hn.of_norm.prod_factor s).comp_injective e.injective
  rw [← e.tsum_eq (fun i => term A σ η hS P ρ X Y Z (s,i)), hs.tsum_prod]
  simp only [term, e, Equiv.prodAssoc_apply, mul_assoc, tsum_mul_left]
end
end DedekindZetaZeroFree.ProbePoissonOrbitFormula
