/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantSheafLeg
public import WeilConjectures.NumberTheory.Padics.IntegersFinite

/-!
# `𝒪_{F,X}` as a free `𝒪_{E,X}`-module of finite rank

Let `E ⊆ F` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. Then `𝒪_F` is a finite free `𝒪_E`-module
with a basis whose coordinate functions are continuous
(`AlgebraicGeometry.ProEtale.exists_basis_integersInclusion`): `𝒪_E^d → 𝒪_F` is a continuous
bijection from a compact space to a Hausdorff space. Hence the abelian sheaf `𝒪_{F,X}` is the
direct sum of copies of `𝒪_{E,X}`: with the coordinates `cⱼ : 𝒪_{F,X} ⟶ 𝒪_{E,X}`
(`AlgebraicGeometry.ProEtale.padicIntegersSheafCoord`) and the multiplications
`o : 𝒪_{E,X} ⟶ 𝒪_{F,X}` (`AlgebraicGeometry.ProEtale.padicIntegersSheafMulOfLE`), we have
`∑ⱼ bⱼ cⱼ = 1` and `cⱼ ∘ o = oⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

section Basis

variable {l : ℕ} [Fact l.Prime] {E F : IntermediateField ℚ_[l] (PadicAlgCl l)}
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (h : E ≤ F)

/-- `𝒪_F` is a finite free `𝒪_E`-module, through `integersInclusion`, with a basis whose
coordinate functions are continuous. -/
theorem exists_basis_integersInclusion :
    letI := (integersInclusion l h).toAlgebra
    letI := normedFieldOfAlgebra l E
    letI := normedFieldOfAlgebra l F
    ∃ (d : ℕ) (b : Module.Basis (Fin d) (integers l E) (integers l F)),
      Continuous b.equivFun := by
  let := (integersInclusion l h).toAlgebra
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower E F (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfin : Module.Finite (integers l E) (integers l F) := finite_integersMap l E F
  have : Module.IsTorsionFree (integers l E) (integers l F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact fun _ _ hxy ↦ Subtype.ext ((IntermediateField.inclusion h).injective
      (congrArg Subtype.val hxy))
  have := Module.free_of_finite_type_torsion_free' (R := integers l E) (M := integers l F)
  let b := Module.finBasis (integers l E) (integers l F)
  refine ⟨_, b, ?_⟩
  let := normedFieldOfAlgebra l E
  let := normedFieldOfAlgebra l F
  have := compactSpace_integers l E
  have := isTopologicalRing_integers l F
  have hc : Continuous b.equivFun.symm := by
    have : (b.equivFun.symm : (Fin _ → integers l E) → integers l F) =
        fun v ↦ ∑ i, integersInclusion l h (v i) * b i := by
      ext v
      simp [Module.Basis.equivFun_symm_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_integersInclusion l h).comp (continuous_apply i)).mul continuous_const
  exact (hc.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)).symm.continuous

end Basis

variable (X : Scheme.{u})

/-- Postcomposition with a continuous additive map `φ : R → Q` between topological rings, as a
morphism of the abelian sheaves `C(-, R) ⟶ C(-, Q)`. -/
noncomputable def continuousMapAbSheafAddHom {R Q : Type} [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] [TopologicalSpace Q] [Ring Q] [IsTopologicalRing Q] (φ : R →+ Q)
    (hφ : Continuous φ) : continuousMapAbSheaf X R ⟶ continuousMapAbSheaf X Q :=
  ⟨{ app _ := AddCommGrpCat.ofHom
      { toFun f := ULift.up ((⟨φ, hφ⟩ : C(R, Q)).comp f.down)
        map_zero' := ULift.ext (ContinuousMap.ext fun _ ↦ map_zero φ)
        map_add' _ _ := ULift.ext (ContinuousMap.ext fun _ ↦ map_add φ _ _) }
     naturality _ _ _ := rfl }⟩

variable {X} {l : ℕ} [Fact l.Prime] {E F : FiniteIntermediateField l}

lemma integersInclusion_refl (x : integers l E.1) : integersInclusion l (le_refl E.1) x = x :=
  rfl

variable (h : E.1 ≤ F.1)

lemma padicIntegersSheafMulOfLE_add (o o' : integers l F.1) :
    padicIntegersSheafMulOfLE X h (o + o') =
      padicIntegersSheafMulOfLE X h o + padicIntegersSheafMulOfLE X h o' := by
  ext U f
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  exact add_mul o o' _

lemma padicIntegersSheafMulOfLE_refl_comp (r : integers l E.1) (o : integers l F.1) :
    padicIntegersSheafMulOfLE X (le_refl E.1) r ≫ padicIntegersSheafMulOfLE X h o =
      padicIntegersSheafMulOfLE X h (integersInclusion l h r * o) := by
  ext U f
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change o * integersInclusion l h (r * f.down x) =
    integersInclusion l h r * o * integersInclusion l h (f.down x)
  rw [map_mul]
  ring

lemma padicIntegersSheafMulOfLE_comp_mapOfLE {F' : FiniteIntermediateField l} (h' : F.1 ≤ F'.1)
    (o : integers l F.1) :
    padicIntegersSheafMulOfLE X h o ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (padicIntegersSheafMapOfLE X l h') =
      padicIntegersSheafMulOfLE X (h.trans h') (integersInclusion l h' o) := by
  ext U f
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change integersInclusion l h' (o * integersInclusion l h (f.down x)) =
    integersInclusion l h' o * integersInclusion l (h.trans h') (f.down x)
  rw [map_mul]
  rfl

section Basis

variable {d : ℕ}
  (b : letI := (integersInclusion l h).toAlgebra
    Module.Basis (Fin d) (integers l E.1) (integers l F.1))
  (hb : letI := (integersInclusion l h).toAlgebra
    letI := normedFieldOfAlgebra l E.1
    letI := normedFieldOfAlgebra l F.1
    Continuous b.equivFun)

include hb in
lemma continuous_basis_coord (j : Fin d) :
    letI := (integersInclusion l h).toAlgebra
    letI := normedFieldOfAlgebra l E.1
    letI := normedFieldOfAlgebra l F.1
    Continuous (b.coord j) :=
  (continuous_apply j).comp hb

variable (X) in
/-- The `j`-th coordinate `𝒪_{F,X} ⟶ 𝒪_{E,X}` in a basis of `𝒪_F` over `𝒪_E` with continuous
coordinates. -/
noncomputable def padicIntegersSheafCoord (j : Fin d) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf X l F.1) ⟶
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf X l E.1) :=
  letI := (integersInclusion l h).toAlgebra
  letI := normedFieldOfAlgebra l E.1
  letI := normedFieldOfAlgebra l F.1
  have := isTopologicalRing_integers l E.1
  have := isTopologicalRing_integers l F.1
  continuousMapAbSheafAddHom X (b.coord j).toAddMonoidHom (continuous_basis_coord h b hb j)

lemma padicIntegersSheafCoord_hom_app (j : Fin d) (U : X.ProEtᵒᵖ)
    (f : (padicIntegersSheaf X l F.1).obj.obj U) (x : U.unop.left) :
    letI := (integersInclusion l h).toAlgebra
    ((padicIntegersSheafCoord X h b hb j).hom.app U f).down x = b.coord j (f.down x) :=
  rfl

lemma sheafHom_app_sum {A B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} {ι : Type*}
    (s : Finset ι) (φ : ι → (A ⟶ B)) (U : X.ProEtᵒᵖ) (f : A.obj.obj U) :
    (∑ j ∈ s, φ j).hom.app U f = ∑ j ∈ s, (φ j).hom.app U f :=
  map_sum ({ toFun ψ := ψ.hom.app U f, map_zero' := rfl, map_add' _ _ := rfl } :
    (A ⟶ B) →+ B.obj.obj U) φ s

/-- `∑ⱼ bⱼ cⱼ(f) = f`. -/
lemma sum_padicIntegersSheafCoord_comp_mul :
    ∑ j, padicIntegersSheafCoord X h b hb j ≫ padicIntegersSheafMulOfLE X h (b j) = 𝟙 _ := by
  let := (integersInclusion l h).toAlgebra
  ext U f
  rw [sheafHom_app_sum]
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  have := b.sum_repr (f.down x)
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at this
  refine Eq.trans ?_ this
  change AddEquiv.ulift (∑ j, (padicIntegersSheafCoord X h b hb j ≫
    padicIntegersSheafMulOfLE X h (b j)).hom.app U f) x = _
  rw [map_sum, ContinuousMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change b j * integersInclusion l h (b.coord j (f.down x)) = _
  rw [mul_comm]
  rfl

/-- `cⱼ(o f) = oⱼ f`. -/
lemma padicIntegersSheafMulOfLE_comp_coord (o : integers l F.1) (j : Fin d) :
    letI := (integersInclusion l h).toAlgebra
    padicIntegersSheafMulOfLE X h o ≫ padicIntegersSheafCoord X h b hb j =
      padicIntegersSheafMulOfLE X (le_refl E.1) (b.repr o j) := by
  let := (integersInclusion l h).toAlgebra
  ext U f
  refine ULift.ext (ContinuousMap.ext fun x ↦ ?_)
  change b.coord j (o * integersInclusion l h (f.down x)) = b.repr o j * f.down x
  have e : integersInclusion l h (f.down x) * o = f.down x • o := (Algebra.smul_def _ _).symm
  rw [mul_comm, e,
    map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]

end Basis

end AlgebraicGeometry.ProEtale
