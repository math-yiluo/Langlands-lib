/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraStr
import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedGlobalSectionsTransport
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSectionsComm
public import WeilConjectures.WeilSheaf.CohomologyProEtale

/-!
# Weil cohomology and its Frobenius from an injective resolution

Let `F` be a Weil sheaf on a `k₀`-scheme `Y` of finite type, with geometric fiber `Ȳ` and
geometric Galois Frobenius `Fr : Ȳ ≅ Ȳ`, and let `I` be an injective resolution of `F` by
pro-étale Weil sheaves. The cohomology `Hʳ(Y ⊗ k̄, F)` is the `r`-th cohomology of the complex
`Γ(Ȳ, I)` of global sections, and its geometric Frobenius is induced by the Frobenius
`Γ(Ȳ, Iⁿ) ≅ Γ(Ȳ, Fr^* Iⁿ) --Γ(φ)--> Γ(Ȳ, Iⁿ)` of the terms of `I`
(`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_resolution`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]


attribute [local instance 2000] CategoryWithHomology.hasHomology

namespace ProEtaleWeilSheaf

variable (k₀ l) (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]

/-- The global sections of a pro-étale Weil sheaf, as a functor to `ℚ̄_ℓ`-modules. -/
noncomputable abbrev globalSectionsWeilFunctor :
    ProEtaleWeilSheaf k₀ l Y ⥤ WeilCoefficients.{u} l :=
  IsoAlgebra.forget _ ⋙ AdicSheaf.forget _ ⋙ Sheaf.Γ _ _

/-- The Frobenius `Γ(Ȳ, M) ≅ Γ(Ȳ, Fr^* M) --Γ(φ)--> Γ(Ȳ, M)` of the global sections of a
pro-étale Weil sheaf `(M, φ)`. -/
@[simps]
noncomputable def globalSectionsFrobeniusNatTrans :
    globalSectionsWeilFunctor k₀ l Y ⟶ globalSectionsWeilFunctor k₀ l Y where
  app X := (globalSectionsLowerStarIso _
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.app X.carrier.X ≫
    (Sheaf.Γ _ _).map ((AdicSheaf.forget _).map X.str.hom)
  naturality X X' φ := by
    have h₁ := (globalSectionsLowerStarIso (WeilCoefficients.{u} l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv.naturality φ.hom.f.hom
    have h₂ := φ.hom.h
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ ⊢
    erw [reassoc_of% h₁]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2
    exact congrArg Mod.Hom.hom h₂

end ProEtaleWeilSheaf

namespace ProEtale

/-- The underlying morphism of sheaves of the Frobenius exchange isomorphism. -/
lemma adicSheafForget_map_adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_app {k : Type u}
    [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)}
    (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) (M : AdicSheaf l f.geometricFiber) :
    ((adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) _ _).hom.app M.X ≫
        (lowerStarCongr (WeilCoefficients.{u} l)
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)).hom.app M.X ≫
          (lowerStarComp (WeilCoefficients.{u} l) _ _).inv.app M.X :=
  rfl

/-- Global sections identify the Frobenius of a commuting square with its structure map. -/
private lemma adicGlobalSections_frobeniusNatTrans_app {Z W : Scheme.{u}} (g : Z ⟶ W)
    (hW : W ⟶ W) (hZ : Z ⟶ Z) (comm : g ≫ hW = hZ ≫ g)
    (X : IsoAlgebra (adicLowerStar l hZ)) :
    (IsoAlgebra.frobeniusNatTrans
      (adicLowerStarComp l g hW ≪≫ adicLowerStarCongr l comm ≪≫
        (adicLowerStarComp l hZ g).symm)
      (adicGlobalSections l W) (adicGlobalSections l Z)
      (adicLowerStarCompGlobalSectionsIso l g)
      (adicLowerStarCompGlobalSectionsIso l hW).inv).app X =
      (adicLowerStarCompGlobalSectionsIso l hZ).inv.app X.carrier ≫
        (adicGlobalSections l Z).map X.str.hom := by
  -- Use naturality and the adic coherence law without unfolding module pushforwards.
  have hnat := (adicLowerStarCompGlobalSectionsIso l g).hom.naturality X.str.hom
  rw [Functor.comp_map] at hnat
  rw [IsoAlgebra.frobeniusNatTrans_app, Functor.map_comp]
  simp only [Category.assoc]
  rw [hnat]
  have h := congrArg (fun f ↦ (adicLowerStarCompGlobalSectionsIso l g).inv.app X.carrier ≫
      f ≫ (adicGlobalSections l Z).map X.str.hom)
    (adicLowerStarCompGlobalSectionsIso_inv_app_comm l g hW hZ g comm X.carrier)
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using h

end ProEtale

namespace WeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

omit [Fact (ringChar k₀ ≠ l)] [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
variable (k₀ l Y) in
/-- The Frobenius of the global sections of the terms of a resolution, in the form of
`CategoryTheory.Endofunctor.IsoAlgebra.frobeniusNatTrans`, is
`AlgebraicGeometry.ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans`. -/
lemma frobeniusNatTrans_eq_globalSectionsFrobeniusNatTrans :
    IsoAlgebra.frobeniusNatTrans (adicLowerStarGeometricFiberMapCompFrobeniusIso l
        (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (Functor.isoWhiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
          (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))))
      (Functor.whiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv) =
      ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans k₀ l Y := by
  refine NatTrans.ext (funext fun X ↦ ?_)
  exact adicGlobalSections_frobeniusNatTrans_app
    (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
      (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) X


/-- **Weil cohomology from an injective resolution.** Let `I` be an injective resolution of a
Weil sheaf `F` by pro-étale Weil sheaves. Then `Hʳ(Y ⊗ k̄, F)` is the `r`-th cohomology of the
complex `Γ(Ȳ, I)`, and its geometric Frobenius is induced by the Frobenius
`Γ(Ȳ, Iⁿ) ≅ Γ(Ȳ, Fr^* Iⁿ) --Γ(φ)--> Γ(Ȳ, Iⁿ)` of the terms of `I`. -/
theorem exists_linearEquiv_cohomology_resolution (F : WeilSheaf k₀ l Y)
    (I : InjectiveResolution F.obj) (r : ℕ) :
    ∃ Θ : (F.cohomology r).carrier ≃ₗ[PadicAlgCl l] (WeilCoefficients.toModuleCat l).obj
        ((I.cocomplex.sc r).map (ProEtaleWeilSheaf.globalSectionsWeilFunctor k₀ l Y)).homology,
      ∀ x, Θ ((F.cohomology r).frobenius x) = ((WeilCoefficients.toModuleCat l).map
        (ShortComplex.homologyMap ((I.cocomplex.sc r).mapNatTrans
          (ProEtaleWeilSheaf.globalSectionsFrobeniusNatTrans k₀ l Y)))).hom (Θ x) := by
  have h := IsoAlgebra.frobenius_globalSectionsHomologyIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l
        (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (Functor.isoWhiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
          (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))))
      (Functor.whiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Spec (CommRingCat.of k₀) ↘
          Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).inv)
      I r
  rw [frobeniusNatTrans_eq_globalSectionsFrobeniusNatTrans] at h
  refine ⟨WeilCoefficients.linearEquivOfIso (IsoAlgebra.globalSectionsHomologyIso
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l
        (Y ↘ Spec (CommRingCat.of k₀)) (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (AdicSheaf.forget _ ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l))
      (Functor.isoWhiskerLeft (AdicSheaf.forget _) (globalSectionsLowerStarIso _
        (Scheme.Hom.geometricFiberMap (Y ↘ Spec (CommRingCat.of k₀))
          (comp_over (Y ↘ Spec (CommRingCat.of k₀)) _)))) I r), fun x ↦ ?_⟩
  exact congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom x) h
end WeilSheaf

end AlgebraicGeometry
