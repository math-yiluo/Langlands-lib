/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Cohomology of pro-étale sheaves of modules and of their underlying abelian sheaves

Let `Λ` be a commutative ring which is torsion free as an abelian group, e.g. `ℚ̄_ℓ`. For a
pro-étale sheaf `G` of `Λ`-modules on a scheme `X`, the derived global sections of `G`, computed
in sheaves of `Λ`-modules, are those of its underlying abelian sheaf. Indeed the forgetful
functor `Φ` from sheaves of `Λ`-modules to abelian sheaves is exact (it is a left adjoint, of
coinduction), and it preserves injective objects, its left adjoint `Λ ⊗_ℤ -` (followed by
sheafification) being exact since `Λ` is flat over `ℤ`.

## Main declarations

- `AlgebraicGeometry.ProEtale.forgetRightDerivedGlobalSectionsIso`: the isomorphism
  `Rᵠ Γ(X_proét, G) ≅ Rᵠ Γ(X_proét, Φ G)` of abelian groups.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The forgetful functor from pro-étale sheaves of `Λ`-modules to abelian sheaves. -/
noncomputable abbrev sheafForget₂ :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  sheafCompose (Scheme.ProEt.topology X) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance : (sheafForget₂ Λ X).Additive where
  map_add {_ _ _ _} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

instance : PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) where
  preservesFiniteLimits _ := ⟨fun {_} ↦ inferInstance⟩

instance : PreservesFiniteColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) where
  preservesFiniteColimits _ := ⟨fun {_} ↦ inferInstance⟩

/-- The forgetful functor to abelian sheaves preserves finite limits, limits of sheaves being
computed on sections. -/
instance preservesFiniteLimits_sheafForget₂ : PreservesFiniteLimits (sheafForget₂ Λ X) := by
  have : PreservesFiniteLimits (sheafForget₂ Λ X ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight (Scheme.ProEt X)ᵒᵖ _ _).obj
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- The forgetful functor to abelian sheaves preserves finite colimits: it is the sheafified
postcomposition with the forgetful functor, which is left adjoint to coinduction. -/
instance preservesFiniteColimits_sheafForget₂ : PreservesFiniteColimits (sheafForget₂ Λ X) := by
  have hadj := ModuleCat.forget₂CoinduceAdj.{u + 1} Λ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coinduce.{u + 1} Λ) :=
    hadj.rightAdjoint_preservesLimits
  have : (Scheme.ProEt.topology X).HasSheafCompose (ModuleCat.coinduce.{u + 1} Λ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction (Scheme.ProEt.topology X) hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- Extension of scalars from abelian groups to modules over a ring which is torsion free as an
abelian group preserves monomorphisms, `Λ` being flat over `ℤ`. -/
lemma preservesMonomorphisms_extendScalarsAddCommGrp [IsAddTorsionFree Λ] :
    (ModuleCat.extendScalarsAddCommGrp Λ).PreservesMonomorphisms := by
  have : HasUniqueDiv Λ :=
    ⟨fun {_} hn {_ _} ↦ eq_of_nsmul_eq_nsmul_of_addCommute hn (add_comm _ _)⟩
  have : (ModuleCat.extendScalars.{0, u + 1, u + 1} (Int.castRingHom Λ)).PreservesMonomorphisms :=
    ⟨fun {M N} f hf ↦ by
      rw [ModuleCat.mono_iff_injective] at hf ⊢
      have hflat (inst : Module ℤ Λ) : Module.Flat ℤ Λ := by
        obtain rfl := Subsingleton.elim inst (AddCommGroup.toIntModule Λ)
        infer_instance
      let : Module ℤ Λ := Module.compHom Λ (Int.castRingHom Λ)
      have := hflat this
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := Λ) f.hom hf⟩
  unfold ModuleCat.extendScalarsAddCommGrp
  infer_instance

/-- Extension of scalars `Λ ⊗_ℤ -` from abelian pro-étale sheaves to sheaves of `Λ`-modules. -/
noncomputable abbrev sheafExtendScalarsAddCommGrp :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ) :=
  Sheaf.composeAndSheafify (Scheme.ProEt.topology X) (ModuleCat.extendScalarsAddCommGrp Λ)

/-- Extension of scalars is left adjoint to the forgetful functor. -/
noncomputable def sheafExtendScalarsAddCommGrpAdjunction :
    sheafExtendScalarsAddCommGrp Λ X ⊣ sheafForget₂ Λ X :=
  Sheaf.adjunction _ (ModuleCat.extendScalarsAddCommGrpAdj Λ)

instance preservesMonomorphisms_sheafExtendScalarsAddCommGrp [IsAddTorsionFree Λ] :
    (sheafExtendScalarsAddCommGrp Λ X).PreservesMonomorphisms := by
  have := preservesMonomorphisms_extendScalarsAddCommGrp Λ
  have : ((Functor.whiskeringRight (Scheme.ProEt X)ᵒᵖ _ _).obj
      (ModuleCat.extendScalarsAddCommGrp Λ)).PreservesMonomorphisms :=
    ⟨fun {F G} f _ ↦ by
      rw [NatTrans.mono_iff_mono_app] at *
      intro U
      exact (ModuleCat.extendScalarsAddCommGrp Λ).map_mono (f.app U)⟩
  unfold sheafExtendScalarsAddCommGrp Sheaf.composeAndSheafify
  infer_instance

/-- The forgetful functor to abelian sheaves preserves injective objects. -/
instance preservesInjectiveObjects_sheafForget₂ [IsAddTorsionFree Λ] :
    (sheafForget₂ Λ X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafExtendScalarsAddCommGrpAdjunction Λ X)

/-- The global sections of a sheaf of `Λ`-modules, as an abelian group, are the global sections
of the underlying abelian sheaf. -/
noncomputable def globalSectionsFunctorCompForget₂Iso :
    globalSectionsFunctor (ModuleCat.{u + 1} Λ) X ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      sheafForget₂ Λ X ⋙ globalSectionsFunctor AddCommGrpCat.{u + 1} X :=
  Iso.refl _

/-- **Cohomology of a sheaf of modules is that of the underlying abelian sheaf.** For a ring `Λ`
which is torsion free as an abelian group and a pro-étale sheaf `G` of `Λ`-modules, the
derived global sections `Rᵠ Γ(X_proét, G)`, as an abelian group, are the derived global
sections of the underlying abelian sheaf. -/
noncomputable def forgetRightDerivedGlobalSectionsIso [IsAddTorsionFree Λ]
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        (((globalSectionsFunctor (ModuleCat.{u + 1} Λ) X).rightDerived q).obj G) ≅
      ((globalSectionsFunctor AddCommGrpCat.{u + 1} X).rightDerived q).obj
        ((sheafForget₂ Λ X).obj G) :=
  (Functor.rightDerivedCompObjIso _ _ q G).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (globalSectionsFunctorCompForget₂Iso Λ X) q G ≪≫
    (Functor.rightDerivedCompIsoOfExact (sheafForget₂ Λ X)
      (globalSectionsFunctor AddCommGrpCat.{u + 1} X) q).app G

end AlgebraicGeometry.ProEtale
