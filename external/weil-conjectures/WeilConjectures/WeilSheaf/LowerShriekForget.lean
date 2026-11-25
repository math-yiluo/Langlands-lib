/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraFreeComparison
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedAdjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFreeInjective
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarCoproducts
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# The direct image with compact support of Weil complexes after forgetting the Weil structure

Let `f : X ⟶ Y` be a morphism of `k₀`-schemes with a compactification `X ⟶[i] Z ⟶[g] Y` over `k₀`.
The direct image with compact support `Rf_! = Rḡ_* ∘ D(ī_!)` of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriek`) is computed, after forgetting the
Weil structures, by the direct image with compact support `Rf̄_! = Rḡ_* ∘ D(ī_!)` of `ℓ`-adic
sheaves on the geometric fibres
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricRightDerivedLowerShriek`): `For ∘ Rf_! ≅ Rf̄_! ∘ For`
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso`).

The morphisms of Weil complexes are computed from the underlying morphisms through free Weil
objects (`CategoryTheory.Endofunctor.IsoAlgebra.bijective_map_comp_of_bijective_forget`), so the
maps `g ↦ Rf_! g ≫ ε` out of `Hom(K, P)` are bijective as soon as `Rf_!` commutes with the free
Weil objects on the shifts of `For K` and the underlying maps `f ↦ Rf̄_! f ≫ For ε` are bijective
(`AlgebraicGeometry.WeilComplex.bijective_map_comp_derivedLowerShriek`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over

open ProEtale

section Compactification

variable (k₀ l)

/-- The direct image with compact support `Rf̄_! = Rḡ_* ∘ D(ī_!)` of `ℓ`-adic pro-étale sheaves on
the geometric fibres, attached to a compactification `X ⟶[i] Z ⟶[g] Y` over `k₀`: the base changes
`ī` and `ḡ` of `i` and `g` to `k̄` form a compactification of the base change `f̄` of `f`. -/
noncomputable def ProEtaleWeilSheaf.geometricRightDerivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⥤
      DerivedCategory (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (Scheme.Hom.geometricFiberMap c.i (comp_over c.i _))_!ᵃ[l].mapDerivedCategory ⋙
    (Scheme.Hom.geometricFiberMap c.g (comp_over c.g _))_*ᵃ[l].rightDerivedFunctor

/-- **Forgetting the Weil structure commutes with the direct image with compact support**:
`For ∘ Rf_! ≅ Rf̄_! ∘ For`, the pasting of `For ∘ D(ī_!) ≅ D(ī_!) ∘ For` and
`For ∘ Rḡ_* ≅ Rḡ_* ∘ For`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] (c : Compactification f) :
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c ⋙
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory ≅
      (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory ⋙
        ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f c := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact Adjunction.compForgetIso
    (Functor.mapDerivedCategoryCompForgetIso (IsoAlgebra.mapOfNatIsoCompForgetIso _))
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _)

end Compactification

section WeilComplex

variable (k₀) (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The compactification of `f` chosen by Nagata's theorem, used to define the direct image with
compact support `Rf₀!` of Weil complexes (`AlgebraicGeometry.WeilComplex.derivedLowerShriek`). -/
noncomputable abbrev WeilComplex.lowerShriekCompactification : Compactification f :=
  HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)

variable {k₀} [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Morphisms out of `Rf₀! K` from the underlying morphisms.** Let `ε : Rf₀! P ⟶ T` be a morphism
of Weil complexes. Suppose that `Rf_!` commutes with the free Weil objects on the shifts of the
underlying complex `For K` of a Weil complex `K`, and that the maps
`Hom(For K[n], For P) ⟶ Hom(Rf̄_! For K[n], For T)`, `φ ↦ Rf̄_! φ ≫ For ε`, are bijective. Then
`g ↦ Rf₀! g ≫ ε` is a bijection `Hom(K, P) ≃ Hom(Rf₀! K, T)`. -/
theorem WeilComplex.bijective_map_comp_derivedLowerShriek {K P : WeilComplex k₀ l X}
    {T : WeilComplex k₀ l Y} (ε : (WeilComplex.derivedLowerShriek k₀ l f).obj P ⟶ T)
    (hc : ∀ n : ℤ, IsIso (Adjunction.freeComparison
      (IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l X))
      (IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l Y))
      (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f (lowerShriekCompactification k₀ f))
      (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f
        (lowerShriekCompactification k₀ f))
      (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
        (lowerShriekCompactification k₀ f))
      ((shiftFunctor _ n).obj (WeilComplex.forget.obj K))))
    (h : ∀ n : ℤ, Function.Bijective fun φ : (shiftFunctor _ n).obj (WeilComplex.forget.obj K) ⟶
        WeilComplex.forget.obj P ↦
      (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f
        (lowerShriekCompactification k₀ f)).map φ ≫
        (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
          (lowerShriekCompactification k₀ f)).inv.app P.obj ≫ WeilComplex.forget.map ε) :
    Function.Bijective fun g : K ⟶ P ↦ (WeilComplex.derivedLowerShriek k₀ l f).map g ≫ ε := by
  have H := IsoAlgebra.bijective_map_comp_of_bijective_forget (WeilSheaf.frobeniusPullback k₀ l X)
    (WeilSheaf.frobeniusPullback k₀ l Y) _ _ _ (P := P.obj) (T := T.obj) ε.hom K.obj hc
    (fun n ↦ ?_)
  swap
  · exact h n
  let e₁ := (ObjectProperty.fullyFaithfulι (WeilComplex.objectProperty k₀ l X)).homEquiv
    (X := K) (Y := P)
  let e₂ := (ObjectProperty.fullyFaithfulι (WeilComplex.objectProperty k₀ l Y)).homEquiv
    (X := (WeilComplex.derivedLowerShriek k₀ l f).obj K) (Y := T)
  have : (fun g : K ⟶ P ↦ (WeilComplex.derivedLowerShriek k₀ l f).map g ≫ ε) =
      e₂.symm ∘ (fun g ↦ (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
        (lowerShriekCompactification k₀ f)).map g ≫ ε.hom) ∘ e₁ := by
    funext g
    exact e₂.injective (by simp [e₁, e₂]; rfl)
  rw [this]
  exact e₂.symm.bijective.comp (H.comp e₁.bijective)

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- **The direct image with compact support commutes with free Weil objects.** For a Weil complex
`K` on `X` and `n : ℤ`, the comparison `Free(Rf̄_! For K[n]) ⟶ Rf_! Free(For K[n])` between the free
pro-étale Weil objects is an isomorphism. -/
theorem WeilComplex.isIso_freeComparison_rightDerivedLowerShriek
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) (n : ℤ) :
    IsIso (Adjunction.freeComparison
      (IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l X))
      (IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l Y))
      (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f (lowerShriekCompactification k₀ f))
      (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f
        (lowerShriekCompactification k₀ f))
      (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
        (lowerShriekCompactification k₀ f))
      ((shiftFunctor _ n).obj (WeilComplex.forget.obj K))) := by
  let c := lowerShriekCompactification k₀ f
  let iBar := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  let gBar := Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀)))
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  -- `Rf_! = Rḡ_* ∘ D(ī_!)`: the free comparison is the composite of those of `D(ī_!)` and `Rḡ_*`
  refine Adjunction.isIso_freeComparison_comp
    (IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l X))
    (IsoAlgebra.freeWeilDerivedAdjunction.{_, _, u + 1} (WeilSheaf.frobeniusPullback k₀ l c.Z))
    (IsoAlgebra.freeWeilDerivedAdjunction (WeilSheaf.frobeniusPullback k₀ l Y)) _ _ _ ?_ ?_
  · -- the extension by zero `ī_!` is exact and commutes with direct sums, being a left adjoint
    have := (ProEtale.adicOpenImmersionLowerShriekAdjunction l iBar).leftAdjoint_preservesColimits
    exact Adjunction.isIso_freeComparison_mapDerivedCategory _ _ _
      (fun S ↦ IsoAlgebra.isIso_freeComparison_mapOfNatIso _ S) _
  · -- `ī_!(For K[n])` is bounded below, so it has a bounded below injective resolution `I`
    obtain ⟨a, ha⟩ := ((ProEtale.adicOpenImmersionLowerShriek l iBar).bounded_mapDerivedCategory_obj
      (ObjectProperty.le_shift (P := DerivedCategory.TStructure.t.bounded) n _
        ((IsoAlgebra.forget _).bounded_mapDerivedCategory_obj K.2.1))).1
    obtain ⟨T, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (hX := ha) _ a
    obtain ⟨I, ι, _, _, _⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T a
    have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
    -- `ḡ_*` commutes with direct sums, and the complex `∐ₙ Fⁿ I` is a bounded below complex of
    -- `ḡ_*`-acyclic objects, so that `Rḡ_*` is computed by `ḡ_*` on it
    have := ProEtale.preservesColimitsOfShape_discrete_adicLowerStar l gBar ℤ
    have h := IsoAlgebra.isIso_freeComparison_rightDerivedFunctor
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g
        (comp_over c.g (Spec (CommRingCat.of k₀)))) I
      (Functor.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE _ _ a fun k ↦
        ProEtale.rightAcyclic_adicLowerStar_sigma_of_injective l gBar _)
    -- `freeWeilDerivedAdjunction` is by definition the derived free adjunction
    exact @Adjunction.isIso_freeComparison_of_iso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (e ≪≫ asIso (DerivedCategory.Q.map ι)) h

end WeilComplex

end AlgebraicGeometry
