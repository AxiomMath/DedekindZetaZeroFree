module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.CotangentCutoffSupport
public import DedekindZetaZeroFree.Adeles.Quotients.HermitianPairings.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualPartitionLocalTest
open KPContActualCutoffSmoothDescent KPContActualCutoffTestPairingHolomorphy
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentOverlapRationalBranches KPContActualCotangentPieceHilbertSum
open KPContActualCotangentCountableShrinking KPContActualSectorFiniteSupportPartition
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {C : KPGlobalTorusInducingPlan.ModelData F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {U : KPMsRationalCompactCrossPairing.Level F ζ hζ}
private theorem coefficient_eq (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ
    (level F ζ hζ C R P H U) R P H)
    (a : ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  simp [sectionFields, LiftedChart.coefficient, isotropyChart, ChartKind.representative]

private theorem local_product {n : ℕ}
    (a : Fin n → ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H)
    {K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U))}
    (Q : FinitePartition F ζ hζ (level F ζ hζ C R P H U) R P H a K O)
    (φ : Tests F ζ hζ C R P H U) (i : Fin n) :
    ∃ τ : localScalarTests (a i),
      (∀ x : omega (a i), τ.val x = (Q.multiplier i (q (a i) x.val) : ℂ) *
        sectionFields φ.val (a i) x) ∧
      HasCompactSupport (liftExtension (a i) τ.val) ∧
      tsupport (liftExtension (a i) τ.val) ⊆ omega (a i) := by
  let f : omega (a i) → ℂ := fun x => (Q.multiplier i (q (a i) x.val) : ℂ) *
    sectionFields φ.val (a i) x
  let g : M F → ℂ := fun x => (Q.lift i (labeledA (placeEquiv F ζ hζ) x) : ℂ) *
    (φ.val (a i).component).val (labeledA (placeEquiv F ζ hζ) x)
  have hf : ∀ x : omega (a i), g x.val = f x := by
    intro x
    have hr := Q.lift_restriction i ⟨labeledA (placeEquiv F ζ hζ) x.val, x.property⟩
    change Q.lift i _ = Q.multiplier i (q (a i) x.val) at hr
    simp only [g, f, hr, coefficient_eq]
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (Complex.ofRealCLM.contDiff.comp ((Q.lift_smooth i).comp
      KPContActualGlobalGreen.contDiff_labeledA)).mul
      ((φ.property.1 (a i).component).comp KPContActualGlobalGreen.contDiff_labeledA)
  have he : liftExtension (a i) f = g := by
    funext x
    by_cases hx : x ∈ omega (a i)
    · simpa [liftExtension, hx] using (hf ⟨x,hx⟩).symm
    · have hz := Q.lift_zero_outside i (labeledA (placeEquiv F ζ hζ) x) hx
      simp [liftExtension, hx, g, hz]
  have hts : tsupport g ⊆ labeledA (placeEquiv F ζ hζ) ⁻¹' tsupport (Q.lift i) := by
    apply closure_minimal _ ((isClosed_tsupport _).preimage
      KPContActualGlobalGreen.contDiff_labeledA.continuous)
    intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [g, hz])
  have hi : tsupport g ⊆ omega (a i) := hts.trans (fun _ hx => Q.lift_support_subset i hx)
  have hcInv : Continuous (labeledAInv (placeEquiv F ζ hζ)) := by
    exact (CotangentLogCoframe.A (d F)).symm.continuous.comp
      (continuous_pi fun k => continuous_apply _)
  have hinv (x : M F) : labeledAInv (placeEquiv F ζ hζ)
      (labeledA (placeEquiv F ζ hζ) x) = x := by
    simp [labeledAInv, labeledA]
  have hcompact : HasCompactSupport g := by
    apply ((Q.lift_compact_support i).image hcInv).of_isClosed_subset (isClosed_tsupport g)
    intro x hx
    exact ⟨labeledA (placeEquiv F ζ hζ) x, hts hx, hinv x⟩
  have hlocal : localSupport (a i) f ⊆ tsupport (Q.multiplier i) := by
    apply closure_minimal _ (isClosed_tsupport _)
    rintro x ⟨y, ⟨hy, hfy⟩, rfl⟩
    apply subset_tsupport
    intro hz
    exact hfy (by simp [f, hz])
  refine ⟨⟨f, ⟨⟨g, hg.contDiffOn, hf⟩, ?_,
    (Q.compact_support i).of_isClosed_subset (isClosed_closure) hlocal,
    hlocal.trans (fun _ hx => (Q.support_subset i hx).1)⟩⟩, fun _ => rfl, ?_, ?_⟩
  · intro γ x hx
    have hcoef := (unitary_phase (isotropyArrow (a i) γ)).2.2.2 φ.val x
      (KPContActualCotangentMeasurableFamilies.omega_subset_larger (a i) hx)
    have hq : q (a i) ((isotropyArrow (a i) γ).psi x) = q (a i) x := by
      change KPFiniteCuspAtlas.componentMap F ζ hζ _ _ _ =
        KPFiniteCuspAtlas.componentMap F ζ hζ _ _ _
      congr 1
      simp only [Arrow.psi, coordinateMap, isotropyArrow, isotropyChart,
        ChartKind.representative, inv_one, one_mul, mul_one]
      have hh (z : KPCuspGenuineMonodromy.SymmetricSpace F) :
          labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
        funext k; simp [labeledA, labeledAInv]
      rw [hh]
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨γ.val.1.val,rfl⟩
    change (Q.multiplier i _ : ℂ) * _ = _
    rw [hq]
    change (Q.multiplier i _ : ℂ) * (isotropyChart (a i)).coefficient φ.val _ = _
    rw [hcoef]
    dsimp [f, sectionFields]
    ring
  · simpa only [he] using hcompact
  · simpa only [he] using hi

theorem localize_test {n : ℕ}
    (a : Fin n → ShrunkChart F ζ hζ (level F ζ hζ C R P H U) R P H)
    {K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ (level F ζ hζ C R P H U))}
    (Q : FinitePartition F ζ hζ (level F ζ hζ C R P H U) R P H a K O)
    (φ : Tests F ζ hζ C R P H U) (i : Fin n) :
    ∃ (ψ : Tests F ζ hζ C R P H U) (τ : localScalarTests (a i)),
      (∀ j z, (ψ.val j).val z =
        (Q.multiplier i (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
          (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z) : ℂ) *
          (φ.val j).val z) ∧
      (∀ x : omega (a i), τ.val x = (Q.multiplier i (q (a i) x.val) : ℂ) *
        sectionFields φ.val (a i) x) ∧
      HasCompactSupport (liftExtension (a i) τ.val) ∧
      tsupport (liftExtension (a i) τ.val) ⊆ omega (a i) := by
  let s : KPContSectorSmoothFramesSupport.Sections F ζ hζ
      (level F ζ hζ C R P H U) R P H := fun j =>
    ⟨fun z => (Q.multiplier i (KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
      (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z) : ℂ) *
        (φ.val j).val z, by
      constructor
      · intro z
        exact Submodule.smul_mem _ _ ((φ.val j).property.1 z)
      · intro γ z
        have hq : KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
            (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j
            ((γ : KPCuspArithmetic.PGL2 F) • z) =
          KPCuspCutoffGraph.basePoint F ζ hζ H.totallyComplex
            (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) j z := by
          apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ _ _)
          apply Quotient.sound
          apply MulAction.orbitRel_apply.mpr
          exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩
        dsimp only
        rw [hq, (φ.val j).property.2 γ z]
        ring⟩
  have hs : s ∈ Tests F ζ hζ C R P H U := by
    constructor
    · intro j
      exact (Complex.ofRealCLM.contDiff.comp
        (Q.smooth i ((H.atlas (level F ζ hζ C R P H U)).representative j))).mul
          (φ.property.1 j)
    · obtain ⟨B,hB,hφB⟩ := φ.property.2
      refine ⟨B,hB,?_⟩
      intro j z hz
      change _ * (φ.val j).val z = 0
      rw [hφB j z hz, mul_zero]
  obtain ⟨τ,hτ,hc,hi⟩ := local_product a Q φ i
  exact ⟨⟨s,hs⟩,τ,fun _ _ => rfl,hτ,hc,hi⟩
end DedekindZetaZeroFree.KPContActualPartitionLocalTest

end
