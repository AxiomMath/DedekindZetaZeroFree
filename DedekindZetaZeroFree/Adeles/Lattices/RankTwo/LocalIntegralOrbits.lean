module

public import DedekindZetaZeroFree.Adeles.Approximation.PGL.BoundedCRT

@[expose] public section

open scoped Pointwise

namespace DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

 abbrev Place (F : Type*) [Field F] [NumberField F] :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

 def evaluation (F : Type*) [Field F] [NumberField F] (v : Place F) :
    Adeles F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

 def evaluatedVector (F : Type*) [Field F] [NumberField F] (v : Place F)
    (x : Matrix (Fin 2) (Fin 1) (Adeles F)) :
    Matrix (Fin 2) (Fin 1) (v.adicCompletion F) := fun i j => x i j v

 def localIntegralVectors (F : Type*) [Field F] [NumberField F] (v : Place F) :
    Set (Matrix (Fin 2) (Fin 1) (v.adicCompletion F)) :=
  {x | ∀ i j, x i j ∈ v.adicCompletionIntegers F}

private lemma evaluatedVector_smul (F : Type*) [Field F] [NumberField F]
    (v : Place F) (g : AdelicGL F)
    (x : Matrix (Fin 2) (Fin 1) (Adeles F)) :
    evaluatedVector F v (g • x) =
      Matrix.GeneralLinearGroup.map (evaluation F v) g • evaluatedVector F v x := by
  change (g.val * x).map (evaluation F v) =
    g.val.map (evaluation F v) * x.map (evaluation F v)
  exact Matrix.map_mul (f := evaluation F v)

private lemma localTranslatedLattice_eq_smul (F : Type*) [Field F] [NumberField F]
    (v : Place F) (g : AdelicGL F) :
    localTranslatedLattice F g v =
      Matrix.GeneralLinearGroup.map (evaluation F v) g • localIntegralVectors F v := rfl

theorem local_lattice_right_orbit (F : Type*) [Field F] [NumberField F] :
    ∀ g g' : AdelicGL F,
      (∀ v, localTranslatedLattice F g v = localTranslatedLattice F g' v) →
        ∃ k : integralGL F, g' = g * k := by
  intro g g' h
  let k : AdelicGL F := g⁻¹ * g'
  have hkLocal (v : Place F) :
      Matrix.GeneralLinearGroup.map (evaluation F v) k • localIntegralVectors F v =
        localIntegralVectors F v := by
    have hv := h v
    rw [localTranslatedLattice_eq_smul, localTranslatedLattice_eq_smul] at hv
    dsimp [k]
    rw [map_mul, map_inv, mul_smul, ← hv, inv_smul_smul]
  have hk : k ∈ integralGL F := by
    change k ∈ MulAction.stabilizer (AdelicGL F) (integralVectors F)
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change (∀ i j v, (k⁻¹ • x) i j v ∈ v.adicCompletionIntegers F) ↔
      (∀ i j v, x i j v ∈ v.adicCompletionIntegers F)
    have hv (v : Place F) :
        evaluatedVector F v (k⁻¹ • x) ∈ localIntegralVectors F v ↔
          evaluatedVector F v x ∈ localIntegralVectors F v := by
      rw [evaluatedVector_smul, map_inv,
        ← Set.mem_smul_set_iff_inv_smul_mem, hkLocal]
    constructor
    · intro hx i j v
      exact (hv v).mp (fun i j => hx i j v) i j
    · intro hx i j v
      exact (hv v).mpr (fun i j => hx i j v) i j
  refine ⟨⟨k, hk⟩, ?_⟩
  simp [k]

end DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers
