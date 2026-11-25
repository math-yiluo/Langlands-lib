/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteEtaleAlgClosed

/-!
# The Leray isomorphism over a finite étale `k₀`-scheme

Let `P` be a finite étale `k₀`-scheme and `f : X ⟶ P` a morphism of `k₀`-schemes. The cohomology
of `P ⊗ k̄` is concentrated in degree `0`, so the Leray spectral sequence of `X ⟶ P ⟶ Spec k₀`
degenerates: `Hⁱ(X ⊗ k̄, F) ≅ Γ(P̄, Rⁱf_* F)` Frobenius-equivariantly.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_globalSections_higherLowerStar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- Transport of a commutative square along isomorphisms: if `α ≫ θ = ε ≫ θ' ≫ β` and
`σ ≫ θ = θ' ≫ τ`, then `(α⁻¹ ≫ ε ≫ σ) ≫ θ = θ ≫ β⁻¹ ≫ τ`. -/
lemma CategoryTheory.Iso.inv_comp_comp_eq_of_hom_comp_eq {C : Type*} [Category C]
    {P Q Q' P' R : C} (α : P ≅ Q) (β : P' ≅ R) (θ : Q ⟶ R) (θ' : Q' ⟶ P') (ε : P ⟶ Q')
    (σ : Q' ⟶ Q) {τ : P' ⟶ R} (h : α.hom ≫ θ = ε ≫ θ' ≫ β.hom) (h' : σ ≫ θ = θ' ≫ τ) :
    (α.inv ≫ ε ≫ σ) ≫ θ = θ ≫ β.inv ≫ τ := by
  simp only [Category.assoc]
  rw [h', Iso.inv_comp_eq, reassoc_of% h]
  simp

namespace AlgebraicGeometry

section GlobalSections

namespace ProEtale

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The invariance `Γ(W, g_* G) ≅ Γ(Z, G)` of global sections under pushforward is compatible
with an exchange isomorphism `g_* ⋙ e_W* ≅ e_Z* ⋙ g_*` coming from a commutative square
`g ≫ e_W = e_Z ≫ g`. -/
lemma globalSectionsLowerStarIso_exchange {Z W : Scheme.{u}} (g : Z ⟶ W) (eZ : Z ⟶ Z)
    (eW : W ⟶ W) (h : g ≫ eW = eZ ≫ g) (G : Sheaf (Scheme.ProEt.topology Z) A) :
    (globalSectionsLowerStarIso A eW).hom.app ((g)_*[A].obj G) ≫
        (globalSectionsLowerStarIso A g).hom.app G =
      (Sheaf.Γ _ A).map ((lowerStarComp A g eW ≪≫ lowerStarCongr A h ≪≫
          (lowerStarComp A eZ g).symm).hom.app G) ≫
        (globalSectionsLowerStarIso A g).hom.app ((eZ)_*[A].obj G) ≫
        (globalSectionsLowerStarIso A eZ).hom.app G := by
  rw [← globalSectionsLowerStarIso_comp, ← globalSectionsLowerStarIso_comp,
    ← globalSectionsLowerStarIso_congr A h]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (Sheaf.Γ _ A) ((lowerStarComp A eZ g).inv.app G),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Y Z : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  (φ : Y ⟶ Z) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ]

omit [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] in
/-- The Frobenius of the global sections of a pushforward `φ_* G` corresponds to that of `G`
under the invariance `Γ(Z̄, φ̄_* G) ≅ Γ(Ȳ, G)` of global sections under pushforward. -/
lemma WeilSheaf.globalSectionsFrobeniusHom_lowerStar_comp (G : WeilSheaf k₀ l Y) :
    globalSectionsFrobeniusHom ((lowerStar φ).obj G) ≫
        (ProEtale.globalSectionsLowerStarIso _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).hom.app G.obj.carrier.X =
      (ProEtale.globalSectionsLowerStarIso _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).hom.app G.obj.carrier.X ≫
        globalSectionsFrobeniusHom G := by
  have key := ProEtale.globalSectionsLowerStarIso_exchange (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ _) G.obj.carrier.X
  have nat := (ProEtale.globalSectionsLowerStarIso _
    (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).hom.naturality
    ((ProEtale.AdicSheaf.forget _).map G.obj.str.hom)
  simp only [globalSectionsFrobeniusHom, lowerStar_obj_obj_str]
  rw [Iso.trans_hom, Functor.map_comp, Functor.map_comp]
  have hε : (Sheaf.Γ _ (WeilCoefficients.{u} l)).map ((ProEtale.AdicSheaf.forget _).map
      ((ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _)).app
        G.obj.carrier).hom) =
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
        ((ProEtale.lowerStarComp (WeilCoefficients.{u} l)
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
          (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≪≫
          ProEtale.lowerStarCongr (WeilCoefficients.{u} l)
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ _) ≪≫
          (ProEtale.lowerStarComp (WeilCoefficients.{u} l)
            (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
            (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).symm).hom.app G.obj.carrier.X) :=
    rfl
  rw [hε]
  have nat' : (Sheaf.Γ _ (WeilCoefficients.{u} l)).map ((ProEtale.AdicSheaf.forget _).map
      ((ProEtale.adicLowerStar l (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).map
        G.obj.str.hom)) ≫
      (ProEtale.globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).hom.app G.obj.carrier.X =
      (ProEtale.globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).hom.app
          ((frobeniusPullback k₀ l Y).obj G.obj.carrier).X ≫
        (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
          ((ProEtale.AdicSheaf.forget _).map G.obj.str.hom) :=
    nat
  have := CategoryTheory.Iso.inv_comp_comp_eq_of_hom_comp_eq
    ((ProEtale.globalSectionsLowerStarIso _
      (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).app
        ((ProEtale.lowerStar (WeilCoefficients.{u} l)
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).obj G.obj.carrier.X))
    ((ProEtale.globalSectionsLowerStarIso _
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).app G.obj.carrier.X)
    _ _ _ _ key nat'
  exact this

/-- The global sections of the pushforward `φ_* G` of a Weil sheaf are those of `G`, with their
Frobenius: `Γ(Z̄, φ̄_* G) ≅ Γ(Ȳ, G)`. -/
noncomputable def WeilSheaf.globalSectionsLowerStarEquiv (G : WeilSheaf k₀ l Y) :
    ((lowerStar φ).obj G).globalSections.Equiv G.globalSections where
  toLinearEquiv := WeilCoefficients.linearEquivOfIso
    ((ProEtale.globalSectionsLowerStarIso _
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).app G.obj.carrier.X)
  map_frobenius x := by
    have h := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom x)
      (WeilSheaf.globalSectionsFrobeniusHom_lowerStar_comp φ G)
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

end GlobalSections

section Derived

open Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]

/-- The pushforward of pro-étale Weil sheaves preserves K-injective complexes: it is right
adjoint to the exact pullback. -/
instance ProEtaleWeilSheaf.preservesKInjectiveComplexes_lowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l φ).PreservesKInjectiveComplexes :=
  (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).preservesKInjectiveComplexes

variable (k₀ l) in
/-- **Composition of derived pushforwards** of pro-étale Weil sheaves:
`R(φ ≫ ψ)_* ≅ Rφ_* ⋙ Rψ_*`. -/
noncomputable def ProEtaleWeilSheaf.rightDerivedLowerStarCompIso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l (φ ≫ ψ)).rightDerivedFunctor ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l ψ).rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompIso' _ _ (ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ)).symm

variable (k₀ l) in
/-- **Degenerate Leray isomorphism**: for an exact pushforward `ψ_*`, the cohomology of
`R(φ ≫ ψ)_* K` is the pushforward along `ψ` of the cohomology of `Rφ_* K`. -/
noncomputable def ProEtaleWeilSheaf.homologyRightDerivedLowerStarCompIso (φ : X ⟶ Y)
    (ψ : Y ⟶ Z) [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))]
    [PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l ψ)]
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) (i : ℤ) :
    (_root_.DerivedCategory.homologyFunctor _ i).obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l (φ ≫ ψ)).rightDerivedFunctor.obj K) ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l ψ).obj ((_root_.DerivedCategory.homologyFunctor _ i).obj
        ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj K)) :=
  (_root_.DerivedCategory.homologyFunctor _ i).mapIso
      ((ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l φ ψ).app K ≪≫
        (ProEtaleWeilSheaf.lowerStar k₀ l ψ).rightDerivedFunctorIsoMapDerivedCategory.app _) ≪≫
    ((Functor.mapDerivedCategoryHomologyFunctorIso _ i).app _).symm

variable (k₀ l) in
/-- **The pushforward along a finite étale `P ⟶ Spec k₀` is exact** on pro-étale Weil sheaves:
its geometric fibre `P̄ ⟶ Spec k̄` is a finite disjoint union of copies of `Spec k̄`
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_isAlgClosed`). -/
lemma ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite_of_etale
    (P : Scheme.{u}) [P.Over (Spec (CommRingCat.of k₀))]
    [IsFinite (P ↘ Spec (CommRingCat.of k₀))] [Etale (P ↘ Spec (CommRingCat.of k₀))] :
    PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l (P ↘ Spec (CommRingCat.of k₀))) := by
  have : IsIso
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsIso (pullback.snd _ _))
  have : IsFinite (P ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsFinite (pullback.snd _ _))
  have : Etale (P ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Etale (pullback.snd _ _))
  have := ProEtale.preservesFiniteColimits_adicLowerStar_of_isAlgClosed l
    (P ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have hg : (P ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure ≫
      inv (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      Scheme.Hom.geometricFiberMap (P ↘ Spec (CommRingCat.of k₀)) (comp_over _ _) := by
    rw [IsIso.comp_inv_eq, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure]
  have : PreservesFiniteColimits
      (ProEtale.adicLowerStar l
        (Scheme.Hom.geometricFiberMap (P ↘ Spec (CommRingCat.of k₀)) (comp_over _ _))) :=
    preservesFiniteColimits_of_natIso (ProEtale.adicLowerStarComp l _ _ ≪≫
      ProEtale.adicLowerStarCongr l hg)
  exact IsoAlgebra.preservesFiniteColimits_mapOfNatIso _

end Derived

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {P : Scheme.{u}} [P.Over (Spec (CommRingCat.of k₀))]
  [IsFinite (P ↘ Spec (CommRingCat.of k₀))] [Etale (P ↘ Spec (CommRingCat.of k₀))]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ P) [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] [QuasiSeparated f]
  [LocallyOfFiniteType f]

/-- **Leray over a finite étale base.** For a morphism `f : X ⟶ P` of `k₀`-schemes to a finite
étale `k₀`-scheme `P` and a Weil sheaf `F` on `X`, `Hⁱ(X ⊗ k̄, F) ≅ Γ(P̄, Rⁱf_* F)` as Frobenius
modules: `Ra_{X*} ≅ Ra_{P*} ∘ Rf_*` for the structure morphisms `a_X`, `a_P`, and the cohomology
of `P ⊗ k̄` is concentrated in degree `0`. -/
theorem nonempty_equiv_cohomology_globalSections_higherLowerStar (F : WeilSheaf k₀ l X)
    (i : ℕ) :
    Nonempty ((F.cohomology i).Equiv ((higherLowerStar f i).obj F).globalSections) := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite_of_etale k₀ l P
  exact ⟨(globalSectionsEquivOfIso (ObjectProperty.isoMk _
    ((_root_.DerivedCategory.homologyFunctor _ i).mapIso
      ((Functor.rightDerivedFunctorNatIso
        (ProEtaleWeilSheaf.lowerStarCongr k₀ l (comp_over f _).symm)).app _) ≪≫
      ProEtaleWeilSheaf.homologyRightDerivedLowerStarCompIso k₀ l f
        (P ↘ Spec (CommRingCat.of k₀)) _ i))).trans
    (globalSectionsLowerStarEquiv (P ↘ Spec (CommRingCat.of k₀)) _)⟩

end AlgebraicGeometry.WeilSheaf
