module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.LevelRestriction
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.ScalarWordBoundaryCenters

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open KPContActualSphericalRightFieldIdentification KPContActualCutoffPlusClearedGerm
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming cutoff → cutoff
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
open _root_.DedekindZetaZeroFree.KPContActualSphericalFlatStage renaming stageConclusions → stageConclusions
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming lift_eq → lift_eq
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {SS : SArithmeticData F} {η : RayClassCharacter F SS.modulus}
variable (AR : PrincipalMellin.ActualRecipe SS η)
variable (AP : KPGlobalTorusFiniteStages.CompatibleModelData F AR.A.zeta12 AR.A.primitive_zeta12)
variable (AC : KPGlobalTorusFiniteStages.LocalFiberData F AR.A.zeta12 AR.A.primitive_zeta12 AP)
variable (D : KPGlobalTorusInducingPlan.ModelData F AR.A.zeta12 AR.A.primitive_zeta12)
variable (Haar : KPSmoothLocalQuotientCharts.HaarRecipe F AR.A.zeta12 AR.A.primitive_zeta12)
variable (Transport : KPMsFixedHaarDisintegration.SphericalTransport F AR.A.zeta12 AR.A.primitive_zeta12)
variable (H : KPMsFixedHaarDisintegration.AllLevels F AR.A.zeta12 AR.A.primitive_zeta12 Haar Transport)
variable (U : KPMsRationalCompactCrossPairing.Level F AR.A.zeta12 AR.A.primitive_zeta12)
local notation "level" => KPContActualAllCuspSource.level F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H U
local notation "G" => KPContSectorCoveredQuotientVocabulary.ActualCover F AR.A.zeta12 AR.A.primitive_zeta12

open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.SphericalScalarProducer renaming word_smul → word_smul
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming compact_word_holomorphy → compact_word_holomorphy
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming singleton_combination → singleton_combination
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.NativeCompactNumerator renaming scalar_eq_lift → scalar_eq_lift
open _root_.DedekindZetaZeroFree.KPContActualCommonDiskRightHolomorphy renaming continuous_of_pieces → continuous_of_pieces
open scoped BigOperators
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralWordChamber renaming literal_finite_word_chamber → literal_finite_word_chamber
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.ConstantTermCovariance.FiniteCompactAssembly renaming finite_compact_numerator → finite_compact_numerator

theorem finite_literal_global_refined_boundary_centers
    (Jaux : KPGlobalTorusFunctionData.FiniteLevel F AR.A.zeta12 AR.A.primitive_zeta12)
    (K : Subgroup G) (hK : IwasawaCompact F AR.A.zeta12 AR.A.primitive_zeta12 K) (f : Flat F AR.A.zeta12 AR.A.primitive_zeta12 K) :
    ∃ (n : ℕ) (U : Fin n → KPMsRationalCompactCrossPairing.Level F AR.A.zeta12 AR.A.primitive_zeta12)
      (m : Fin n → ℕ)
      (v : ∀ i, Fin (m i) → KPContActualSphericalFlatStage.Stage F AR.A.zeta12 AR.A.primitive_zeta12 (U i))
      (w : ∀ i, Fin (m i) → List (Fin (groupDimension F)))
      (B : ∀ i, Fin (m i) → ℂ → ℂ)
      (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i))
      (z : ∀ i, Fin (m i) → KPContActualAllCuspSource.Sector F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i)),
      (∀ i, KPShift81CoherentLevel.level F AR.A.zeta12 AR.A.primitive_zeta12 (U i) = U i) ∧
      (∀ i, (U i).toOpenSubgroup.toSubgroup ≤ Jaux.toOpenSubgroup.toSubgroup) ∧
      (∀ i j, KPContActualSmoothLineGluing.Represents F AR.A.zeta12 AR.A.primitive_zeta12
        (KPContActualAllCuspSource.level F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i)) Haar Transport H (Z i j).val (z i j)) ∧
      (∀ i j, (z i j, KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) 0 • z i j) ∈
        (sourceLaplacian F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i)).graph) ∧
      (∀ i j, LiteralSource.SphericalBoundaryProperty AR AP AC D Haar Transport H (U i) (v i j) (z i j)) ∧
      (∀ i j g, KPMsGreenFlux.casimir F AR.A.zeta12 AR.A.primitive_zeta12
        (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j)) g =
        KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) 0 *
          groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j) g) ∧
      (∀ i j, KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
        F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j) → Z i j = 0) ∧
      (∀ g, f.val 0 g = ∑ i, ∑ j, B i j 0 * actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 (w i j)
        ((KPContFlatSourceRecipe.flatR F AR.A.zeta12 AR.A.primitive_zeta12 0 (v i j).val).val) g) ∧
      ∃ (Q : ℂ → ℂ) (S T : ℂ → G → ℂ) (r : ℝ),
        AnalyticOnNhd ℂ Q KPContinuation.spectralDomain ∧ Q 0 = 1 ∧
        (∀ g, MeromorphicOn (fun s => S s g) KPContinuation.spectralDomain) ∧
        (∀ s, (1 : ℝ)/3 < s.re → ∀ g, S s g = Q s * eisenstein F AR.A.zeta12 AR.A.primitive_zeta12 K f s g) ∧
        0 < r ∧ Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain ∧
        (∀ g, AnalyticOnNhd ℂ (fun s => T s g) (Metric.ball (0 : ℂ) r)) ∧
        (∀ s ∈ Metric.ball (0 : ℂ) r, s ≠ 0 → T s = s • S s) ∧
        ∀ g, T 0 g = ∑ i, ∑ j, B i j 0 * actualRightWord F AR.A.zeta12 AR.A.primitive_zeta12 (w i j)
          (groupScalar F AR.A.zeta12 AR.A.primitive_zeta12 D Haar Transport H (U i) (Z i j)) g := by
  obtain ⟨n, Uold, m, vold, w, Q, B, hQ, hQ0, ⟨r₀, hr₀, hb₀, _⟩, hB, hrec, hch⟩ :=
    literal_finite_word_chamber F AR.A.zeta12 AR.A.primitive_zeta12 K hK f
  let U := fun i => KPShift81CoherentLevel.level F AR.A.zeta12 AR.A.primitive_zeta12
    (ResidualBoundaryRelevel.meetLevel F AR.A.zeta12 AR.A.primitive_zeta12 (Uold i) Jaux)
  have hle (i) : (U i).toOpenSubgroup.toSubgroup ≤ (Uold i).toOpenSubgroup.toSubgroup :=
    (KPShift81CoherentLevel.level_le F AR.A.zeta12 AR.A.primitive_zeta12 _).trans inf_le_left
  let v := fun i j => ResidualBoundaryRelevel.restrictStage F AR.A.zeta12 AR.A.primitive_zeta12 (Uold i) (U i) (hle i) (vold i j)
  have hfix (i) : KPShift81CoherentLevel.level F AR.A.zeta12 AR.A.primitive_zeta12 (U i) = U i :=
    ResidualBoundaryRelevel.level_idempotent F AR.A.zeta12 AR.A.primitive_zeta12 _
  have haux (i) : (U i).toOpenSubgroup.toSubgroup ≤ Jaux.toOpenSubgroup.toSubgroup :=
    (KPShift81CoherentLevel.level_le F AR.A.zeta12 AR.A.primitive_zeta12 _).trans inf_le_right
  have hp (i : Fin n) (j : Fin (m i)) :=
    spherical_word_scalar_hilbert_boundary_producer AR AP AC D Haar Transport H (U i) (v i j) (w i j)
  choose A N hAc hAm r hr hb hclear hNa hNj Z z hz heig horth hnative hcenter hcus using hp
  have hall : ∀ᶠ s in 𝓝 (0 : ℂ),
      s ∈ Metric.ball (0 : ℂ) r₀ ∧ ∀ i j, s ∈ Metric.ball (0 : ℂ) (r i j) := by
    apply Filter.Eventually.and (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀))
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr i j))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨n, U, m, v, w, B, Z, z, hfix, haux, hz, heig, horth, hnative, hcus, ?_, Q,
    (fun s g => ∑ i, ∑ j, B i j s * A i j s g),
    (fun s g => ∑ i, ∑ j, B i j s * N i j s g), ρ, hQ, hQ0, ?_, ?_, hρ,
    fun s hs => hb₀ (hρsub hs).1, ?_, ?_, ?_⟩
  · intro g
    simpa only [hQ0, one_mul, v, ResidualBoundaryRelevel.restrictStage_val] using hrec 0 (by norm_num [KPContinuation.spectralDomain]) g
  · intro g s hs
    apply MeromorphicAt.fun_sum
    intro i _
    apply MeromorphicAt.fun_sum
    intro j _
    exact ((hB i j) s hs).meromorphicAt.mul (hAm i j g s hs)
  · intro s hs g
    simp_rw [hAc _ _ s hs]
    exact (hch s hs g).symm
  · intro g s hs
    apply Finset.univ.analyticAt_fun_sum
    intro i _
    apply Finset.univ.analyticAt_fun_sum
    intro j _
    exact ((hB i j) s (hb₀ (hρsub hs).1)).mul
      (hNa i j g s ((hρsub hs).2 i j))
  · intro s hs hn
    funext g
    simp_rw [hclear _ _ s ((hρsub hs).2 _ _) hn, Pi.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro g
    simp_rw [hcenter]

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
