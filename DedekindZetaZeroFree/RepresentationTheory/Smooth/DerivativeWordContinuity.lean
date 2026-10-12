module

public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology
public import DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DerivativeWordLinearity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualWordSpatial
open KPSmoothActualFlowData
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem word_right_invariant (f : X F ζ hζ → ℂ) (u : G F ζ hζ)
    (hu : ∀ a : GInfinity F, Commute (archimedeanInsertion F ζ hζ a) u)
    (hf : ∀ g : G F ζ hζ, f (Quotient.mk _ (g * u)) = f (Quotient.mk _ g))
    (w : List (B F)) (g : G F ζ hζ) :
    wordDerivative F ζ hζ w f (Quotient.mk _ (g * u)) =
      wordDerivative F ζ hζ w f (Quotient.mk _ g) := by
  induction w generalizing g with
  | nil => exact hf g
  | cons b w ih =>
    change deriv _ 0 = deriv _ 0
    apply congrArg (fun q : ℝ → ℂ => deriv q 0)
    funext t
    change wordDerivative F ζ hζ w f
      (Quotient.mk _ ((g * u) * archimedeanInsertion F ζ hζ (flow F b t))) =
      wordDerivative F ζ hζ w f
        (Quotient.mk _ (g * archimedeanInsertion F ζ hζ (flow F b t)))
    rw [mul_assoc, (hu (flow F b t)).eq.symm, ← mul_assoc]
    exact ih _

theorem word_continuous_at_finite_level
    (W : OpenSubgroup (KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ))
    (f : X F ζ hζ → ℂ) (hf : SmoothAutomorphic F ζ hζ f)
    (hlevel : ∀ g : G F ζ hζ, ∀ u : W,
      f (Quotient.mk _ (g * (u.val : G F ζ hζ))) = f (Quotient.mk _ g))
    (w : List (B F)) : Continuous (wordDerivative F ζ hζ w f) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  change (GInfinity F × KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ) ≃ₜ* G F ζ hζ at e
  change ∀ (a : GInfinity F) (k : KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ),
    e (a,k) = archimedeanInsertion F ζ hζ a * k at he
  have hcomm (a : GInfinity F)
      (k : KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ) :
      Commute (archimedeanInsertion F ζ hζ a) (k : G F ζ hζ) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a k
  have hinv (g : G F ζ hζ) (u : W) :
      wordDerivative F ζ hζ w f (Quotient.mk _ (g * (u.val : G F ζ hζ))) =
        wordDerivative F ζ hζ w f (Quotient.mk _ g) :=
    word_right_invariant F ζ hζ f _ (fun a => hcomm a u.val)
      (fun g => hlevel g u) w g
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  apply e.toHomeomorph.isQuotientMap.continuous_iff.mpr
  apply continuous_iff_continuousAt.mpr
  intro p
  rcases p with ⟨a, k⟩
  have ho := ActualWordLinearity.word_orbit_continuous F ζ hζ f hf w (Quotient.mk _ (k : G F ζ hζ))
  have hc : ContinuousAt (fun p : GInfinity F × KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ =>
      wordDerivative F ζ hζ w f (Quotient.mk _ (archimedeanInsertion F ζ hζ p.1 * k))) (a,k) := by
    convert (ho.comp continuous_fst).continuousAt using 1
    funext p
    change wordDerivative F ζ hζ w f (Quotient.mk _ (archimedeanInsertion F ζ hζ p.1 * k)) =
      wordDerivative F ζ hζ w f (Quotient.mk _ ((k : G F ζ hζ) * archimedeanInsertion F ζ hζ p.1))
    rw [(hcomm p.1 k).eq]
  apply hc.congr_of_eventuallyEq
  have hn : ∀ᶠ p : GInfinity F × KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ in 𝓝 (a,k),
      k⁻¹ * p.2 ∈ W :=
    (continuous_const.mul continuous_snd).continuousAt.preimage_mem_nhds (by
      simpa using W.isOpen.mem_nhds W.one_mem)
  filter_upwards [hn] with p hp
  change wordDerivative F ζ hζ w f (Quotient.mk _ (e p)) =
    wordDerivative F ζ hζ w f (Quotient.mk _ (archimedeanInsertion F ζ hζ p.1 * k))
  rcases p with ⟨b, l⟩
  rw [he]
  have h := hinv (archimedeanInsertion F ζ hζ b * k) ⟨k⁻¹ * l, hp⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using h

 theorem finitePart_eq : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    KPSmoothLocalQuotientCharts.finiteSubgroup F ζ hζ := by
  unfold KPGlobalTorusFunctionData.finitePart KPSmoothLocalQuotientCharts.finiteSubgroup
  congr 1
  ext x
  simp [KPSmoothLocalQuotientCharts.finiteTuples, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem word_continuous (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : X F ζ hζ → ℂ) (hf : SmoothAutomorphic F ζ hζ f)
    (hlevel : ∀ g : G F ζ hζ, ∀ u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      f (Quotient.mk _ (g * u.val)) = f (Quotient.mk _ g))
    (w : List (B F)) : Continuous (wordDerivative F ζ hζ w f) := by
  have h : ∀ g : G F ζ hζ, ∀ u : U.toOpenSubgroup,
      f (Quotient.mk _ (g * (u.val : G F ζ hζ))) = f (Quotient.mk _ g) := by
    intro g u
    exact hlevel g ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩
  clear hlevel
  revert h
  change CompactOpenLevel (KPGlobalTorusFunctionData.finitePart F ζ hζ) at U
  revert U
  rw [finitePart_eq F ζ hζ]
  intro U h
  exact word_continuous_at_finite_level F ζ hζ U.toOpenSubgroup f hf h w

end DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualWordSpatial

end
