module

public import DedekindZetaZeroFree.Eisenstein.Sections.SmoothIwasawaLogNorm
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology BigOperators NNReal
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy
open KPLiteralRaw KPLiteralChamber
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def discrepancy (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (g : G F ζ hζ) : ℝ :=
  Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
    (literalIwasawa F ζ hζ K hK) g : NNReal) : ℝ)) -
  KPContFlatFullProductIwasawa.alpha F ζ hζ g

private theorem log_borel (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) : NNReal) : ℝ)) =
    Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) +
      Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : NNReal) : ℝ)) := by
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul]
  simp only [Units.val_mul, NNReal.coe_mul]
  exact Real.log_mul (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
    (NNReal.coe_ne_zero.mpr (Units.ne_zero _))

 theorem discrepancy_borel (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    discrepancy F ζ hζ K hK ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      discrepancy F ζ hζ K hK g := by
  unfold discrepancy KPContFlatFullProductIwasawa.alpha
  rw [log_borel, log_borel]
  ring

private theorem insertion_mem (K : Subgroup (G F ζ hζ))
    (h : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2),
      KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈ K)
    (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
    PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w))) ∈ K := by
  rw [show PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ from rfl,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  apply list_prod_mem
  intro k hk
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hk
  exact h w (u w)

private theorem discrepancy_eq_finiteComponent (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (g : G F ζ hζ) :
    discrepancy F ζ hζ K hK g = discrepancy F ζ hζ K hK
      (KPContFlatLogNormSmooth.finiteComponent F ζ hζ g) := by
  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  obtain ⟨y, x, u, hfac, hy⟩ :=
    KPContFlatArchProjectionNorm.archimedean_factorization F ζ hζ a
  let k := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w)))
  have hk : k ∈ K := insertion_mem F ζ hζ K hK.2.2 u
  have hkD : k ∈ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K :=
    insertion_mem F ζ hζ _ (KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ) u
  have hfin : KPContFlatLogNormSmooth.finiteComponent F ζ hζ g ∈
      PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
    apply RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
    change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (KPContFlatLogNormSmooth.finiteComponent F ζ hζ g) = 1
    unfold KPContFlatLogNormSmooth.finiteComponent
    rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    simp
  have hc : Commute k (KPContFlatLogNormSmooth.finiteComponent F ζ hζ g) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _ ⟨_, hfin⟩
  have hg : g = ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
      KPGlobalTorusFunctionData.N F ζ hζ x) *
      KPContFlatLogNormSmooth.finiteComponent F ζ hζ g) * k := by
    calc
      g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a *
          KPContFlatLogNormSmooth.finiteComponent F ζ hζ g := by
        dsimp [a, KPContFlatLogNormSmooth.finiteComponent]; group
      _ = _ := by rw [hfac]; dsimp [k] at hc ⊢; rw [mul_assoc, hc.eq, ← mul_assoc]
  conv_lhs => rw [hg]
  unfold discrepancy KPContFlatFullProductIwasawa.alpha
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact
      F ζ hζ (literalIwasawa F ζ hζ K hK) _ ⟨k, hk⟩,
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact
      F ζ hζ (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ) _ ⟨k, hkD⟩]
  change discrepancy F ζ hζ K hK
    ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (y w : ℂ))).val *
      KPGlobalTorusFunctionData.N F ζ hζ x * KPContFlatLogNormSmooth.finiteComponent F ζ hζ g) = _
  exact discrepancy_borel F ζ hζ K hK _ _ _

 theorem discrepancy_locallyConstant (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) :
    IsLocallyConstant (discrepancy F ζ hζ K hK) := by
  let c : G F ζ hζ → KPGlobalTorusFunctionData.finitePart F ζ hζ := fun g =>
    ⟨KPContFlatLogNormSmooth.finiteComponent F ζ hζ g,
      KPContFlatLogNormSmooth.finiteComponent_mem F ζ hζ g⟩
  have hc : Continuous c := by
    have hsplit := RepresentationTheory.ArchFiniteSplitting.splitting_maps_continuous F ζ hζ
    exact (((hsplit.1.comp hsplit.2).inv).mul continuous_id).subtype_mk _
  have hKlc :=
    KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.iwasawaNorm_finite_locallyConstant
      (F := F) (ζ := ζ) (hζ := hζ) (D := literalIwasawa F ζ hζ K hK)
  have hDlc :=
    KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.iwasawaNorm_finite_locallyConstant
      (F := F) (ζ := ζ) (hζ := hζ) (D := KPContFlatFullProductIwasawa.iwasawaData F ζ hζ)
  have h := ((hKlc.comp (fun n : (ℝ≥0)ˣ => Real.log ((n : ℝ≥0) : ℝ))).comp₂
    (hDlc.comp (fun n : (ℝ≥0)ˣ => Real.log ((n : ℝ≥0) : ℝ))) (· - ·)).comp_continuous hc
  convert h using 1
  funext g
  exact discrepancy_eq_finiteComponent F ζ hζ K hK g

 theorem discrepancy_range_finite (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) :
    (Set.range (discrepancy F ζ hζ K hK)).Finite := by
  let D := KPContFlatFullProductIwasawa.iwasawaData F ζ hζ
  let : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  have h := (discrepancy_locallyConstant F ζ hζ K hK).comp_continuous
    (continuous_subtype_val : Continuous (fun k : D.K => (k : G F ζ hζ)))
  apply h.range_finite.subset
  rintro v ⟨g, rfl⟩
  obtain ⟨t, x, k, hg⟩ := D.decomposition g
  refine ⟨k, ?_⟩
  rw [hg, discrepancy_borel]
  rfl

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy

end

section

noncomputable section
open scoped NumberField Classical Topology BigOperators NNReal
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy
open KPLiteralRaw KPLiteralChamber
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem literal_reweight_finite_expansion (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ C : Finset ℝ, ∀ (s : ℂ) (g : G F ζ hζ),
      Complex.exp (-s * (KPContFlatFullProductIwasawa.alpha F ζ hζ g : ℂ)) * f.val s g =
        ∑ a ∈ C, Complex.exp (s * (a : ℂ)) *
          (if discrepancy F ζ hζ K hK g = a then f.val 0 g else 0) := by
  let C := (discrepancy_range_finite F ζ hζ K hK).toFinset
  refine ⟨C, ?_⟩
  intro s g
  have hmem : discrepancy F ζ hζ K hK g ∈ C :=
    (Set.Finite.mem_toFinset _).mpr (Set.mem_range_self g)
  rw [Finset.sum_eq_single (discrepancy F ζ hζ K hK g)]
  · rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK]
    simp only [ite_true]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    unfold discrepancy
    rw [Complex.ofReal_sub]
    ring
  · intro b hb hne
    simp [Ne.symm hne]
  · exact fun h => (h hmem).elim

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.NormDiscrepancy

end
end
