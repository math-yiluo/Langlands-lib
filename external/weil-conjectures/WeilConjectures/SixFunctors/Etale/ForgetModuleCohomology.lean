/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExactAcyclic
public import WeilConjectures.CategoryTheory.Sites.CechInjectiveModule
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Étale cohomology of sheaves of modules over any ring

Let `Λ` be a ring and `X` a quasi-compact quasi-separated scheme. For an étale sheaf `G` of
`Λ`-modules on `X`, the derived global sections `Rᵠ Γ(X_ét, G)`, computed in sheaves of
`Λ`-modules, are, as an abelian group, the cohomology of the underlying abelian sheaf
(`AlgebraicGeometry.Etale.forgetRightDerivedSectionsIso`). The forgetful functor is exact and
sends injective sheaves of `Λ`-modules to acyclic abelian sheaves, by the Čech criterion
(`CategoryTheory.Sheaf.subsingleton_H_succ_forget₂_of_injective`); no flatness of `Λ` over `ℤ`
is needed. This applies to `Λ = ℤ/ℓᵐ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The forgetful functor from étale sheaves of `Λ`-modules to abelian étale sheaves. -/
noncomputable abbrev sheafForget₂ :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance : (sheafForget₂ Λ X).Additive where
  map_add {_ _ _ _} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

instance preservesFiniteLimits_sheafForget₂ : PreservesFiniteLimits (sheafForget₂ Λ X) := by
  have : PreservesFiniteLimits (sheafForget₂ Λ X ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance preservesFiniteColimits_sheafForget₂ : PreservesFiniteColimits (sheafForget₂ Λ X) := by
  have hadj := ModuleCat.forget₂CoinduceAdj.{u + 1} Λ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coinduce.{u + 1} Λ) :=
    hadj.rightAdjoint_preservesLimits
  have : X.smallEtaleTopology.HasSheafCompose (ModuleCat.coinduce.{u + 1} Λ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction X.smallEtaleTopology hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- **Injective étale sheaves of modules are acyclic as abelian sheaves**, on a quasi-compact
quasi-separated scheme, by the Čech criterion. -/
theorem rightAcyclic_sheafForget₂_obj_of_injective [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    (sectionsFunctor AddCommGrpCat.{u + 1} X).rightAcyclic ((sheafForget₂ Λ X).obj I) := by
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let B : X.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
        (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := Scheme.exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (Scheme.ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine Scheme.compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  intro q
  have hH := Sheaf.subsingleton_H_succ_forget₂_of_injective hT B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov I q
  obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology T hT ((sheafForget₂ Λ X).obj I) q
  have : Subsingleton (((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived (q + 1)).obj
      ((sheafForget₂ Λ X).obj I)) := e.symm.toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- **Cohomology of a sheaf of modules is that of the underlying abelian sheaf**, for any ring
`Λ`: on a quasi-compact quasi-separated scheme, the derived global sections `Rᵠ Γ(X_ét, G)`,
computed in sheaves of `Λ`-modules, are, as an abelian group, those of the underlying abelian
sheaf. -/
noncomputable def forgetRightDerivedSectionsIso [CompactSpace X] [QuasiSeparatedSpace X]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((sectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived q).obj G) ≅
      ((sectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived q).obj
        ((sheafForget₂ Λ X).obj G) :=
  (Functor.rightDerivedCompObjIso _ _ q G).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (Iso.refl (sectionsFunctor (ModuleCat.{u + 1} Λ) X ⋙
      forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≪≫ Iso.refl _) q G ≪≫
    (Functor.rightDerivedCompIsoOfExactOfRightAcyclic (sheafForget₂ Λ X)
      (sectionsFunctor AddCommGrpCat.{u + 1} X)
      (fun I _ ↦ rightAcyclic_sheafForget₂_obj_of_injective Λ X I) q).app G

end AlgebraicGeometry.Etale
