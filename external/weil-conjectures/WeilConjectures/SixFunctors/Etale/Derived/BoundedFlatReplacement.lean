/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
public import WeilConjectures.SixFunctors.Etale.Derived.TensorResolution

/-!
# Functorial bounded above flat replacements of complexes of étale sheaves

Every bounded above complex `K` of étale sheaves (with values in a coefficient category `A`
with functorial flat resolutions, e.g. `A = ModuleCat Λ`) has a functorial flat replacement:
a bounded above complex `Φ(K)` of flat sheaves, vanishing in the degrees where `K` strictly
vanishes from some degree `N` on, with a termwise epimorphic quasi-isomorphism `Φ(K) ⟶ K`
(`AlgebraicGeometry.Etale.exists_boundedAbove_flat_replacement`, blueprint
`proposition-open-direct-image-preserves-finite`).

`Φ(K)` is the total complex of the bicomplex obtained by resolving each term `Kᵖ` by the
functorial flat resolution of `A`
(`CategoryTheory.Abelian.LeftResolution.minusResolutionFunctor`). The quasi-isomorphism
`Φ(K) ⟶ K` restricts on the summand `(n, 0)` of `Φ(K)ⁿ` to the epimorphism `π : F(Kⁿ) ⟶ Kⁿ` of
the resolution, hence it is a termwise epimorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory HomologicalComplex₂

namespace AlgebraicGeometry.Etale

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The component in degree `n` of the quasi-isomorphism `Φ(K) ⟶ K` attached to a left
resolution, restricted to the summand `(n, 0)` of the total complex. -/
lemma _root_.CategoryTheory.Abelian.LeftResolution.ιTotal_totalπ_f {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C] [Abelian D]
    {ι : C ⥤ D} [ι.Full] [ι.Faithful] [ι.Additive] (Λ : Abelian.LeftResolution ι)
    [Λ.F.PreservesZeroMorphisms] (K : CochainComplex.Minus D) (n : ℤ) :
    ι.map ((Λ.bicomplexFunctor.obj K.obj).ιTotal (ComplexShape.up ℤ) n 0 n (by simp)) ≫
        (Λ.totalπ K).f n =
      ((Λ.bicomplexπ.app K.obj).f n).f 0 ≫
        ((singleRow D (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0).obj K.obj).ιTotal
          (ComplexShape.up ℤ) n 0 n (by simp) ≫ (singleRow₀ObjTotal K.obj).hom.f n := by
  simp [Abelian.LeftResolution.totalπ, Abelian.LeftResolution.totalπ', mapTotalIso]

/-- The quasi-isomorphism `Φ(K) ⟶ K` attached to a left resolution is a termwise epimorphism:
on the summand `(n, 0)` of `Φ(K)ⁿ` it is the epimorphism `π : F(Kⁿ) ⟶ Kⁿ` of the resolution. -/
lemma _root_.CategoryTheory.Abelian.LeftResolution.epi_totalπ_f {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [HasZeroObject C] [HasFiniteCoproducts C] [Abelian D]
    {ι : C ⥤ D} [ι.Full] [ι.Faithful] [ι.Additive] (Λ : Abelian.LeftResolution ι)
    [Λ.F.PreservesZeroMorphisms] (K : CochainComplex.Minus D) (n : ℤ) :
    Epi ((Λ.totalπ K).f n) := by
  have h := Λ.ιTotal_totalπ_f K n
  have : IsIso (((singleRow D (ComplexShape.up ℤ) (ComplexShape.up ℤ) 0).obj K.obj).ιTotal
      (ComplexShape.up ℤ) n 0 n (by simp)) := by
    rw [singleRow_ιTotal]
    infer_instance
  have : Epi (((Λ.bicomplexπ.app K.obj).f n).f 0) := by
    change Epi ((Λ.cochainComplexπ (K.obj.X n)).f 0)
    rw [Abelian.LeftResolution.cochainComplexπ_f_0]
    infer_instance
  have : Epi (ι.map ((Λ.bicomplexFunctor.obj K.obj).ιTotal (ComplexShape.up ℤ) n 0 n
      (by simp)) ≫ (Λ.totalπ K).f n) := by
    rw [h]
    infer_instance
  exact epi_of_epi (ι.map ((Λ.bicomplexFunctor.obj K.obj).ιTotal (ComplexShape.up ℤ) n 0 n
    _)) ((Λ.totalπ K).f n)

/-- The resolution `Φ(K)` of a complex `K` strictly concentrated in degrees `≤ N` is strictly
concentrated in degrees `≤ N`. -/
lemma _root_.CategoryTheory.Abelian.LeftResolution.isStrictlyLE_minusResolutionFunctor_obj
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [HasZeroObject C]
    [HasFiniteCoproducts C] [Abelian D] {ι : C ⥤ D} [ι.Full] [ι.Faithful]
    (Λ : Abelian.LeftResolution ι) [Λ.F.PreservesZeroMorphisms] (K : CochainComplex.Minus D)
    (N : ℤ) [K.obj.IsStrictlyLE N] : (Λ.minusResolutionFunctor.obj K).obj.IsStrictlyLE N :=
  inferInstanceAs (CochainComplex.IsStrictlyLE
    ((Λ.bicomplexFunctor.obj K.obj).total (ComplexShape.up ℤ)) N)

/-- Blueprint `proposition-open-direct-image-preserves-finite`: Functorial bounded-above flat
replacement.

There is a functor `Φ` on bounded above complexes of étale sheaves on `X` together with a
natural transformation `π : Φ ⟶ 𝟭` such that for every bounded above complex `K`: the terms of
`Φ(K)` are flat, `π_K : Φ(K) ⟶ K` is a quasi-isomorphism and a termwise epimorphism, and `Φ(K)`
is strictly concentrated in degrees `≤ N` whenever `K` is. In particular every bounded above
complex of étale sheaves of `Λ`-modules is quasi-isomorphic to a bounded above complex of flat
sheaves. Here `Φ(K)` is the total complex of the termwise functorial flat resolutions of `K`
(`CategoryTheory.Abelian.LeftResolution.minusResolutionFunctor`). -/
theorem exists_boundedAbove_flat_replacement :
    ∃ (Φ : CochainComplex.Minus (Sheaf X.smallEtaleTopology A) ⥤
        CochainComplex.Minus (Sheaf X.smallEtaleTopology A)) (π : Φ ⟶ 𝟭 _),
      (∀ K n, ObjectProperty.flat ((Φ.obj K).obj.X n)) ∧
      (∀ K, QuasiIso (π.app K).hom) ∧
      (∀ K n, Epi ((π.app K).hom.f n)) ∧
      (∀ K (N : ℤ), K.obj.IsStrictlyLE N → (Φ.obj K).obj.IsStrictlyLE N) := by
  let Λ : Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ Sheaf X.smallEtaleTopology A) :=
    (Classical.arbitrary _ : Abelian.LeftResolution _).reduced
  have : Λ.F.PreservesZeroMorphisms :=
    inferInstanceAs (Abelian.LeftResolution.reduced _).F.PreservesZeroMorphisms
  refine ⟨Λ.minusResolutionFunctor ⋙ ObjectProperty.flat.ι.mapCochainComplexMinus,
    Λ.minusResolutionNatTrans, fun K n ↦ ((Λ.minusResolutionFunctor.obj K).obj.X n).property,
    fun K ↦ inferInstance, fun K n ↦ ?_, fun K N hK ↦ ?_⟩
  · change Epi ((Λ.totalπ K).f n)
    exact Λ.epi_totalπ_f K n
  · rw [CochainComplex.isStrictlyLE_iff] at hK ⊢
    intro i hi
    have : CochainComplex.IsStrictlyLE K.obj N := (CochainComplex.isStrictlyLE_iff _ _).2 hK
    have := Λ.isStrictlyLE_minusResolutionFunctor_obj K N
    exact ObjectProperty.flat.ι.map_isZero
      (CochainComplex.isZero_of_isStrictlyLE (Λ.minusResolutionFunctor.obj K).obj N i (by omega))

end AlgebraicGeometry.Etale
