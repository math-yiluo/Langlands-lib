/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# The open–closed triangle under direct image with compact support

For a closed immersion `i : Z ↪ X` with open complement `j : U ↪ X` of separated `k₀`-schemes of
finite type, applying `Ra_!` to the open–closed localization triangle `j_!j^*K → K → i_*i^*K →` of
a Weil complex `K` on `X` gives a distinguished triangle

`Ra_{U!} j^*K ⟶ Ra_{X!} K ⟶ Ra_{Z!} i^*K ⟶`

of Weil complexes on `Spec k₀` (blueprint `prop-functor-package`, clause 3). This file deduces it
and identifies the pullback of a Weil sheaf placed in degree zero with the pullback of the sheaf.

## Main declarations

- `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed`:
  the triangle.
- `AlgebraicGeometry.WeilSheaf.toComplexCompUpperStarIso`: `φ^* (F[0]) ≅ (φ^* F)[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- `Rf₀!` only depends on the morphism `f`, not on the proofs of its properties: equal morphisms
have isomorphic direct images with compact support. -/
noncomputable def WeilComplex.derivedLowerShriekIsoOfEq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f g : X ⟶ Y}
    (h : f = g) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    derivedLowerShriek k₀ l f ≅ derivedLowerShriek k₀ l g :=
  eqToIso (by subst h; rfl)

/-- **The open–closed triangle under `Ra_!`**: for a closed immersion `i : Z ↪ X` with open
complement `j : U ↪ X` of separated `k₀`-schemes of finite type and a Weil complex `K` on `X`,
there is a distinguished triangle of Weil complexes on `Spec k₀`

`Ra_{U!} j^*K ⟶ Ra_{X!} K ⟶ Ra_{Z!} i^*K ⟶ Ra_{U!} j^*K[1]`,

obtained by applying `Ra_{X!}` to the open–closed recollement triangle `j_!j^*K → K → i_*i^*K →`
(`AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed` for the structure
morphism `a_X`), using `a_X ∘ j = a_U` and `a_X ∘ i = a_Z`. -/
theorem WeilComplex.exists_distTriang_derivedLowerShriek_structure_openClosed {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (K : WeilComplex k₀ l X) :
    ∃ (α : (derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar j).obj K) ⟶
        (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K)
      (β : (derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K ⟶
        (derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar i).obj K))
      (γ : (derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar i).obj K) ⟶
        ((derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).obj
          ((WeilComplex.upperStar j).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (WeilComplex k₀ l (Spec (CommRingCat.of k₀))) := by
  have hj : j ≫ X ↘ Spec (CommRingCat.of k₀) = U ↘ Spec (CommRingCat.of k₀) :=
    comp_over j _
  have hi : i ≫ X ↘ Spec (CommRingCat.of k₀) = Z ↘ Spec (CommRingCat.of k₀) :=
    comp_over i _
  have : QuasiCompact (j ≫ X ↘ Spec (CommRingCat.of k₀)) := by rw [hj]; infer_instance
  have : QuasiCompact j := QuasiCompact.of_comp j (X ↘ Spec (CommRingCat.of k₀))
  have hc : IsCompl (Set.range j.base) (Set.range i.base) := by
    rw [hij]; exact isCompl_compl
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_derivedLowerShriek_openClosed j i hc (X ↘ Spec (CommRingCat.of k₀)) K
  let e₁' := e₁ ≪≫ (derivedLowerShriekIsoOfEq hj).app _
  let e₃' := e₃ ≪≫ (derivedLowerShriekIsoOfEq hi).app _
  refine ⟨e₁'.inv ≫ T.mor₁ ≫ e₂.hom, e₂.inv ≫ T.mor₂ ≫ e₃'.hom,
    e₃'.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁'.hom,
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e₁'.symm e₂.symm e₃'.symm ?_ ?_ ?_)⟩
  · simp
  · simp
  · simp [← Functor.map_comp]

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf placed in
degree zero: the pullback of pro-étale Weil sheaves is exact. -/
noncomputable def WeilSheaf.toComplexCompUpperStarIso :
    WeilSheaf.toComplex ⋙ WeilComplex.upperStar φ ≅
      WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⋙ WeilSheaf.toComplex :=
  ((WeilComplex.objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((ProEtaleWeilSheaf.upperStar k₀ l φ).mapDerivedCategorySingleFunctor
        0) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry
