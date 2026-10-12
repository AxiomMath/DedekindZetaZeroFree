module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormTwistedPeriodizationAndAveraging

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Pointwise
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance smoothTopology2 (P : Polarization F ζ hζ) :
    TopologicalSpace (Smooth F ζ hζ P) :=
  KPGlobalTorusFunctionData.torusSmoothTopology F ζ hζ P

abbrev GroupArch := InfinitePlace F → Fin 3 → ℂ

def groupArchDomain : Set (GroupArch F) := {z | ∀ w, z w 1 ≠ 0}

def groupArchTuple (z : GroupArch F) : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ := by
  refine ⟨fun v => ?_, ?_⟩
  · cases v with
    | inl w =>
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)
      let y : w.Completionˣ := if h : z w 1 = 0 then 1
        else Units.mk0 (e.symm (z w 1)) (by
          intro h0
          apply h
          simpa using congrArg e h0)
      exact KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (z w 0)) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) y *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (z w 2))
    | inr q => exact 1
  · apply Filter.Eventually.of_forall
    intro v
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q => exact Subgroup.one_mem _

def groupArchChart (z : GroupArch F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (groupArchTuple F ζ hζ z))

 theorem groupArchDomain_open : IsOpen (groupArchDomain F) := by
  have h : groupArchDomain F = ⋂ w : InfinitePlace F, {z : GroupArch F | z w 1 ≠ 0} := by
    ext z
    simp [groupArchDomain]
  rw [h]
  apply isOpen_iInter_of_finite
  intro w
  exact isOpen_ne_fun ((continuous_apply 1).comp (continuous_apply w)) continuous_const

def InducedFunctions (P : Polarization F ζ hζ) :
    Submodule ℂ (G F ζ hζ → Smooth F ζ hζ P) where
  carrier := {f | ∀ (t : E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ),
    f ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ t •
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f g)}
  zero_mem' := by
    intro t x g
    simp
  add_mem' := by
    intro f k hf hk t x g
    simp only [Pi.add_apply, hf t x g, hk t x g, map_add, smul_add]
  smul_mem' := by
    intro c f hf t x g
    simp only [Pi.smul_apply, hf t x g, map_smul]
    exact smul_comm _ _ _

def InducedLevel (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    Submodule ℂ (InducedFunctions F ζ hζ P) where
  carrier := {f | (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (f.val (groupArchChart F ζ hζ z * g)).val.val 1) (groupArchDomain F)) ∧
    ∀ (g : G F ζ hζ) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      f.val (g * j.val) = f.val g}
  zero_mem' := by
    constructor
    · intro g; exact contDiffOn_const
    · intro g j; rfl
  add_mem' := by
    intro f k hf hk
    constructor
    · intro g; exact (hf.1 g).add (hk.1 g)
    · intro g j
      change f.val (g * j.val) + k.val (g * j.val) = f.val g + k.val g
      rw [hf.2 g j, hk.2 g j]
  smul_mem' := by
    intro c f hf
    constructor
    · intro g; exact contDiffOn_const.smul (hf.1 g)
    · intro g j
      change c • f.val (g * j.val) = c • f.val g
      rw [hf.2 g j]

def Induced (P : Polarization F ζ hζ) : Submodule ℂ (InducedFunctions F ζ hζ P) :=
  ⨆ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, InducedLevel F ζ hζ P J

local instance inducedFunctionsAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (InducedFunctions F ζ hζ P) := @Submodule.addCommGroup ℂ (G F ζ hζ → Smooth F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedFunctions F ζ hζ P)

local instance inducedLevelAddGroup (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    AddCommGroup (InducedLevel F ζ hζ P J) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (InducedLevel F ζ hζ P J)

local instance inducedAddGroup (P : Polarization F ζ hζ) :
    AddCommGroup (Induced F ζ hζ P) := @Submodule.addCommGroup ℂ (InducedFunctions F ζ hζ P)
      inferInstance inferInstance inferInstance (Induced F ζ hζ P)

def inducedJetBound (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ P J) : ℝ :=
  sSup ((fun z => ‖iteratedFDerivWithin ℝ n
    (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
    (groupArchDomain F) z‖) '' K.set)

private theorem jet_image_bdd (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ P J) :
    BddAbove ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
  apply K.compact.bddAbove_image
  apply ContinuousOn.mono _ K.inside
  exact ((f.property.1 g).continuousOn_iteratedFDerivWithin (by simp)
    (groupArchDomain_open F).uniqueDiffOn).norm

 theorem inducedJetBound_add_le (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f h : InducedLevel F ζ hζ P J) :
    inducedJetBound F ζ hζ P J g n K (f + h) ≤
      inducedJetBound F ζ hζ P J g n K f + inducedJetBound F ζ hζ P J g n K h := by
  by_cases hK : K.set.Nonempty
  · apply csSup_le (hK.image _)
    rintro r ⟨z, hz, rfl⟩
    have hzU := K.inside hz
    change ‖iteratedFDerivWithin ℝ n
      ((fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1) +
       (fun y => (h.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ ≤ _
    rw [iteratedFDerivWithin_add_apply
      ((f.property.1 g z hzU).of_le (by simp))
      ((h.property.1 g z hzU).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn hzU]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup (jet_image_bdd F ζ hζ P J g n K f) (Set.mem_image_of_mem _ hz))
      (le_csSup (jet_image_bdd F ζ hζ P J g n K h) (Set.mem_image_of_mem _ hz)))
  · have hE : K.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
    simp [inducedJetBound, hE, Real.sSup_empty]

private theorem norm_jet_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} {v : V} {n : ℕ} {f : V → ℂ} (c : ℂ)
    (hf : ContDiffWithinAt ℝ n f s v) (hs : UniqueDiffOn ℝ s) (hv : v ∈ s) :
    ‖iteratedFDerivWithin ℝ n (c • f) s v‖ =
      ‖c‖ * ‖iteratedFDerivWithin ℝ n f s v‖ := by
  rw [iteratedFDerivWithin_const_smul_apply (R := ℂ) hf hs hv, norm_smul]

 theorem inducedJetBound_smul (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (c : ℂ) (f : InducedLevel F ζ hζ P J) :
    inducedJetBound F ζ hζ P J g n K (c • f) = ‖c‖ * inducedJetBound F ζ hζ P J g n K f := by
  unfold inducedJetBound
  have hEq : (fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => ((c • f).val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set =
      ‖c‖ • ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set) := by
    change _ = (fun r : ℝ => ‖c‖ • r) '' ((fun z => ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖) '' K.set)
    rw [Set.image_image]
    apply Set.image_congr
    intro z hz
    change ‖iteratedFDerivWithin ℝ n
      (c • (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1))
      (groupArchDomain F) z‖ = ‖c‖ * ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖
    exact norm_jet_smul c
      ((f.property.1 g z (K.inside hz)).of_le (by simp))
      (groupArchDomain_open F).uniqueDiffOn (K.inside hz)
  rw [hEq]
  exact Real.sSup_smul_of_nonneg (α := ℝ) (norm_nonneg c) _

def inducedJet (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)) :
    Seminorm ℂ (InducedLevel F ζ hζ P J) :=
  Seminorm.of (inducedJetBound F ζ hζ P J g n K)
    (inducedJetBound_add_le F ζ hζ P J g n K) (inducedJetBound_smul F ζ hζ P J g n K)

def inducedLevelTopology (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    TopologicalSpace (InducedLevel F ζ hζ P J) :=
  (SeminormFamily.moduleFilterBasis
    (fun i : G F ζ hζ × ℕ × KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) =>
      inducedJet F ζ hζ P J i.1 i.2.1 i.2.2)).topology

def inducedStageInclusion (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    InducedLevel F ζ hζ P J →ₗ[ℂ] Induced F ζ hζ P :=
  Submodule.inclusion (le_iSup (fun J => InducedLevel F ζ hζ P J) J)

def inducedFinalSeminorms (P : Polarization F ζ hζ) :=
  {q : Seminorm ℂ (Induced F ζ hζ P) // ∀ J,
    @Continuous (InducedLevel F ζ hζ P J) ℝ
      (inducedLevelTopology F ζ hζ P J) inferInstance
      (q ∘ inducedStageInclusion F ζ hζ P J)}

def inducedTopology (P : Polarization F ζ hζ) : TopologicalSpace (Induced F ζ hζ P) :=
  (SeminormFamily.moduleFilterBasis
    (fun q : inducedFinalSeminorms F ζ hζ P => q.val)).topology

end
end DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport
